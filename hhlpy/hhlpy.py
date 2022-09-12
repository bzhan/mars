"""
Python implementation of Hybrid Hoare Logic.

This version uses data structures that are separate from the main
HCSP program.

"""
import copy

from sympy import sympify, degree, symbols, factor_list, fraction, simplify

from hhlpy.sympy_wrapper import sp_polynomial_div, sp_simplify, sp_is_polynomial
from hhlpy.wolframengine_wrapper import solveODE, wl_prove
from hhlpy.wolframengine_wrapper import wl_simplify, wl_polynomial_div, wl_is_polynomial, found_wolfram
from hhlpy.z3wrapper import z3_prove
from ss2hcsp.hcsp import hcsp, expr, assertion, label
from ss2hcsp.hcsp.parser import expr_parser, expr_parser
from ss2hcsp.hcsp.simulator import get_pos


def compute_diff(e, eqs_dict, functions):
    """Compute differential of an arithmetic or boolean expression."""
    def rec(e):
        if isinstance(e, expr.LogicExpr):
            if e.op == "&&":
                return expr.LogicExpr("&&", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == "||":
                return expr.LogicExpr("&&", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == "->":
                return rec(expr.LogicExpr("||", expr.neg_expr(e.exprs[0]), e.exprs[1]))
            elif e.op == "!":
                return rec(expr.neg_expr(e.exprs[0]))
            else:
                raise NotImplementedError
        elif isinstance(e, expr.RelExpr):
            if e.op == '<' or e.op == '<=':
                return expr.RelExpr("<=", rec(e.expr1), rec(e.expr2))
            elif e.op == '>' or e.op == '>=':
                return expr.RelExpr(">=", rec(e.expr1), rec(e.expr2))
            elif e.op == '==' or e.op == '!=':
                return expr.RelExpr("==", rec(e.expr1), rec(e.expr2))
            else:
                raise NotImplementedError
        elif isinstance(e, expr.AConst):
            return expr.AConst(0)
        elif isinstance(e, expr.BConst):
            return expr.BConst(True)
        elif isinstance(e, expr.FunExpr):
            if len(e.exprs) == 0:
                return expr.AConst(0)      
            elif e.fun_name in functions:
                return rec(expr.replace_function(e, functions))
            else:
                raise NotImplementedError
        elif isinstance(e, expr.AVar):
            if e.name in eqs_dict:
                return eqs_dict[e.name]
            else:
                return expr.AConst(0)
        elif isinstance(e, expr.OpExpr):
            if len(e.exprs) == 1:
                return expr.OpExpr("-", rec(e.exprs[0]))
            elif e.op == '+':
                return expr.OpExpr("+", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '-':
                return expr.OpExpr("-", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '*':
                # d(u*v) = u*dv + du*v
                du, dv = rec(e.exprs[0]), rec(e.exprs[1])
                return expr.OpExpr("+", expr.OpExpr("*", e.exprs[0], dv), 
                                        expr.OpExpr("*", du, e.exprs[1]))
            elif e.op == '^' and isinstance(e.exprs[1], expr.AConst):
                # d(u^n) = n * u^(n-1) * du
                du = rec(e.exprs[0])
                mid_expr = expr.OpExpr("^", e.exprs[0], expr.OpExpr("-", e.exprs[1], expr.AConst(1)))
                return expr.OpExpr("*", e.exprs[1], expr.OpExpr("*", mid_expr, du)) 
            elif e.op == '/':
                # d(u/v) = (du * v - u * dv)/ v^2   u'v-uv')/v²
                # If v is constant, d(u/v) = 1/v * du, which is easier than using above rule.
                if isinstance(e.exprs[1], expr.AConst) or \
                   isinstance(e.exprs[1], expr.FunExpr) and len(e.exprs == 0): # actually a constant
                    du = rec(e.exprs[0])
                    return expr.OpExpr('*', expr.OpExpr('/', expr.AConst(1), e.exprs[1]), du)
                else:
                    du = rec(e.exprs[0])
                    dv = rec(e.exprs[1])
                    numerator = expr.OpExpr("-", expr.OpExpr("*", du, e.exprs[1]), expr.OpExpr("*", e.exprs[0], dv))
                    denominator = expr.OpExpr('*', e.exprs[1], e.exprs[1])
                    return expr.OpExpr('/', numerator, denominator)            
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError
    return rec(e)

def constraint_examination(e):
    '''Examine whether the constraint is open intervals or not.'''
    if not isinstance(e, expr.Expr):
        raise NotImplementedError
    
    def rec(e):
        if isinstance(e, expr.RelExpr):
            if e.op in [">", "<", "!="]:
                return True
            else:
                return False
        elif isinstance(e, expr.LogicExpr):
            if e.op == '!':
                return not rec(e.exprs[0])
            elif e.op == '&&' or e.op == '||':
                return rec(e.exprs[0] and e.exprs[1])
    return rec(e)

def compute_boundary(e):
    # Compute the boundary for a boolean expression.
    if isinstance(e, expr.RelExpr):
        if e.op in ['<', '>', '!=']:
            return expr.RelExpr("==", e.expr1, e.expr2)
    elif isinstance(e, expr.LogicExpr):
        if e.op == '&&':
            boundary1 = compute_boundary(e.exprs[0])
            boundary2 = compute_boundary(e.exprs[1])
            disj1 = expr.LogicExpr('&&', e.exprs[0], boundary2)
            disj2 = expr.LogicExpr('&&', e.exprs[1], boundary1)
            disj3 = expr.LogicExpr('&&', boundary1, boundary2)
            return expr.list_disj(disj1, disj2, disj3)
        elif e.op == '||':
            boundary1 = compute_boundary(e.exprs[0])
            boundary2 = compute_boundary(e.exprs[1])
            neg1 = expr.neg_expr(e.exprs[0])
            neg2 = expr.neg_expr(e.exprs[1])
            disj1 = expr.LogicExpr('&&', neg1, boundary2)
            disj2 = expr.LogicExpr('&&', neg2, boundary1)
            return expr.LogicExpr('||', disj1, disj2)
        elif e.op == '!':
            return compute_boundary(expr.neg_expr(e.exprs[0]))
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError

def compute_closed_set(e):
    """Compute the closed set for an open interval"""
    if isinstance(e, expr.RelExpr):
        if e.op == '<':
            return expr.RelExpr("<=", e.expr1, e.expr2)
        elif e.op == '>':
            return expr.RelExpr(">=", e.expr1, e.expr2)
        elif e.op == '!=':
            return expr.true_expr
        else:
            raise NotImplementedError

    elif isinstance(e, expr.LogicExpr):
        if e.op == '&&':
            return expr.LogicExpr('&&', compute_closed_set(e.exprs[0]), compute_closed_set(e.exprs[1]))
        elif e.op == '||':
            return expr.LogicExpr('||', compute_closed_set(e.exprs[0]), compute_closed_set(e.exprs[1]))
        elif e.op == '!':
            return compute_closed_set(expr.neg_expr(e))
        else:
            raise NotImplementedError

    else:
        raise NotImplementedError

# Return the relexpression 'denomibator != 0' for term e.           
def demoninator_not_zero(e):
    if not isinstance(e, expr.Expr):
        raise NotImplementedError

    if not isinstance(e, str):
        e = str(e)
    
    e = simplify(sympify(e.replace('^', '**')))
    _, denominator = fraction(e)
    denominator = expr_parser.parse(str(denominator).replace('**', '^'))

    return expr.RelExpr('!=', denominator, expr.AConst(0))

# Create a new AVar by adding suffix.
# s is the root var name, names is the set of names being used.
def create_newvar(s, names):
    if not isinstance(s, str):
        raise AssertionError
    # If s is already a new variable name, return the AVar object of s.
    if s not in names:
        return expr.AVar(s)
    # Increase the suffix number until it's a new variable name.
    suffix_n = 1
    while (s + str(suffix_n) in names):
        suffix_n = suffix_n + 1
    return expr.AVar(s + str(suffix_n))


class CmdInfo:
    """Information associated to each HCSP program branch."""
    def __init__(self):
        # Pre-condition and post-condition are assertions.
        self.pre = None
        self.post = None

        # List of verification conditions for this command.
        self.vcs = []

        # Type of the parent program.
        self.parent_type = None

        # Equation dict for ODEs.
        self.eqs_dict = dict()

        # Assumptions for HCSPs.
        self.assume = []

        # Invariants for loop at this position.
        self.inv = []

        # Use differential weakening rule or not
        # It's True by default, which means we apply dw rule on ODE by default.
        # After applying dw rule, set dw to be False and one of the other rules to be True to verify invariants. 
        self.dw = True

        # Use solution axiom or not
        self.sln_rule = False

        # Use the trivial semantics or not.(True and False is the invariant for all ODEs)
        self.tv = False

        # Use differiential invariant rule.
        self.dI_rule = False

        # Invariants in differiential invariant for ODEs.
        self.dI_inv = None

        # Differential cuts for ODEs.
        self.diff_cuts = []

        # dG invariants for ODEs.
        self.dG_inv = None

        # Ghost invariants for new ODEs in which ghost equation is added.
        self.ghost_inv = None

        # Names of related ghost variables
        # Note that it does not include all ghost variable names of the ODE, but the related ones in this branch.
        # For example, in the branch with invariant x * y > 0, ghost z is not in ghost_vars.
        self.ghost_vars = []

        # Computed differential equations for ghosts.
        self.ghost_eqs = dict()

        # Use darboux rule for ODEs.
        self.dbx_rule = False

        # Invariants in dbx rule or ODEs.
        self.dbx_inv = None

        # Dbx cofactor for ODEs
        self.dbx_cofactor = None

        # Use barrier certificate rule or not
        self.barrier_rule = False 

        # Add barrier invariant for ODEs.
        self.barrier_inv = None

        # Use conjunction rule
        self.conj_rule = False

        # Use andR rule
        self.andR = False

    def __str__(self):
        res = ""
        res += "pre = %s\n" % self.pre
        res += "post = %s\n" % self.post
        for vc in self.vcs:
            res += "vc: %s\n" % vc
        if self.inv is not None:
            res += "inv: %s\n" % self.inv
        if self.ghost_inv is not None:
            res += "ghost_inv: %s\n" % self.ghost_inv
        if self.ghost_eqs is not None:
            for ghost_var, eq in self.ghost_eqs.items():
                res += "ghost_eq: %s_dot = %s\n" % (ghost_var, str(eq))
        for diff_cut in self.diff_cuts:
            res += "diff_cut: %s\n" % diff_cut

        return res

class Condition:
    """Stores a condition(pre-condition, post-condition, verification condition) and the parts of the program that it originates from."""
    def __init__(self, expr, path=[], origins=[], blabel=None, blabel_depth=0, bottom_loc=None, categ=None, isVC=False):
        # The expression stating the condition itself
        self.expr = expr
        # The positions of hps where the condition originates from
        self.path = path
        # The locations of assertions and expressions that the condition originates from
        self.origins = origins
        # The location of the bottom-most assertion assocated with the condition
        self.bottom_loc = bottom_loc
        # The category of VC, used in VC generated by loop and ODE,
        # which can be "init" or "maintain"
        self.categ = categ

        # The depth at which new branch labels are added while computing a wp,
        # only acquired when the Condition is a computed wp, otherwise, set as 0 by default.
        self.blabel_depth = blabel_depth

        # The branch label of this condition 
        self.blabel = blabel

        # Whether this condition is a verification condition or not
        self.isVC = isVC

        if self.isVC:
            # Compute the composite label when vc is True
            if self.categ and self.blabel:
                self.comp_label = label.CompLabel(categ_label=label.CategLabel(categ=self.categ),
                                                  branch_label=self.blabel)
            elif self.categ and not self.blabel:
                self.comp_label = label.CategLabel(categ=self.categ)
            elif not self.categ and self.blabel:
                self.comp_label = self.blabel
            else:
                self.comp_label = None

            # The solver used to verify this verification condition.
            # Set as 'z3' by default.
            self.solver = 'z3'

    def __str__(self):
        return str(self.expr)


class OriginLoc:
    """Location of an assertion(pre-condition, post-condition, invariant) or expression
    that a Condition originates from"""
    def __init__(self, index=None, isPre=False, isPost=False, isInv=False, isGhost=False, isConstraint=False, hp_pos=None):
        # The index of the assertion
        self.index = index
        # Whether it is pre-condition of the whole program
        self.isPre = isPre
        # Whether it is post-condition of the whole program
        self.isPost = isPost
        # Whether it is invariant
        self.isInv = isInv
        # Whether it is a ghost introduction
        self.isGhost = isGhost
        # Whether it is ode constraint
        self.isConstraint = isConstraint
        # Only required if it is an invariant or constraint.
        # The position of the hcsp program, to which the invariant is attached.
        self.hp_pos = hp_pos


class CmdVerifier:
    """Contains current state of verification of an HCSP program."""
    def __init__(self, *, pre, hp, post, functions=dict()):
        # The HCSP program to be verified.
        self.hp = hp

        # The list of post conditions of the whole HCSP program
        self.post = post

        # Mapping from program position to CmdInfo objects.
        self.infos = dict()

        # The conjunction of post expression
        pre_conj = expr.list_conj(*[subpre.expr for subpre in pre])
        # The conjunction of post expression
        post_conj = expr.list_conj(*[subpost.expr for subpost in post])

        # Dictionary of declared functions
        # TODO: Use this below instead of scanning the expressions?
        self.functions = functions

        # Set of function names that are used
        fun_names = hp.get_fun_names().union(pre_conj.get_fun_names(), post_conj.get_fun_names())

        # Set of var_names that are used, the names of AVar expression 
        var_names = hp.get_vars().union(pre_conj.get_vars(), post_conj.get_vars())

        # Set of names(function names and var_names) that are used
        self.names = fun_names.union(var_names)

        # Set of program variables that are used
        self.variable_names = set()
        self.compute_variable_set()

        # Set of functions with zero arity that are used, which can be treated as constants
        zero_arity_funcs = hp.get_zero_arity_funcs().union(pre_conj.get_zero_arity_funcs(), post_conj.get_zero_arity_funcs())

        self.constant_names = zero_arity_funcs.union(var_names - self.variable_names)

        # Initialize info for the root object. Place pre-condition and post-condition.
        # pos is a pair of two tuples. 
        # pos[0] is the position of the sub_hp in hp.
        # pos[1] is the number of subproof of the same sub_hp
        root_pos = ((),())
        self.infos[root_pos] = CmdInfo()
        self.infos[root_pos].pre = [Condition(expr=subpre.expr, 
                                              origins=[OriginLoc(isPre=True, index=idx)]) 
                                        for idx, subpre in enumerate(pre)]
        self.infos[root_pos].post = [Condition(expr=subpost.expr, 
                                               origins=[OriginLoc(isPost=True, index=idx)],
                                               bottom_loc=OriginLoc(index=idx, isPost=True)
                                               ) 
                                        for idx, subpost in enumerate(post)]

        # If there are pre-conditions of constants in the form: A op c, 
        # in which A is a constant symbol, c doesn't include variable symbols, op is in RelExpr.op
        # the pre-conditions will always hold.
        # Add this kind of pre-conditions into assumptions in HCSPs.
        for subpre in self.infos[root_pos].pre:
            subpre_expr = subpre.expr
            # Replace the FunExpr by corresponding LogicExpr or OpExpr
            subpre_expr = expr.subst_all_funcs(subpre_expr, self.functions)

            # Split the subpre_expr if it is a conjunction, for example, A >= 0 && x >= A
            subpre_exprs = expr.split_conj(subpre_expr)
            for sub_expr in subpre_exprs:
                # vars is not empty and does not include variable names.
                if (sub_expr.get_vars() or sub_expr.get_fun_names()) \
                 and sub_expr.get_vars().isdisjoint(self.variable_names):
                    self.infos[root_pos].assume.append(Condition(expr=sub_expr,
                                                                 origins=subpre.origins))

    def set_andR_rule(self, pos, andR):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].andR = andR

    def __str__(self):
        res = ""
        for pos, info in self.infos.items():
            res += str(pos) + ":\n"
            res += str(info)
        return res
    
    def print_info(self):
        res = ""
        for pos, info in self.infos.items():
            res += "%s:\n%s" % (pos, info)
        return res

    def simplify_expression(self, e):
        if found_wolfram:
            e = wl_simplify(e, self.functions)

        # Use sympy to simplify
        else:
            e = sp_simplify(e, self.functions)

        return e

    def polynomial_div(self, p, q, constants):
        """Compute the quotient and remainder of polynomial p and q"""
        if found_wolfram:
            quot_remains = wl_polynomial_div(p, q, constants, self.functions)
        else:
            quot_remains = sp_polynomial_div(p, q, self.functions)

        return quot_remains

    def is_polynomial(self, e, constants=set()): 
        """Return True if the given expression is a polynomial, and False otherwise."""
        if found_wolfram:
            result = wl_is_polynomial(e, self.functions, constants)
        else:
            result = sp_is_polynomial(e, self.functions, constants)

        return result

    def compute_variable_set(self, pos=tuple()):
        """Compute variable name set for hcsp program, in which variable values can be changed by Assign, RandomAssign and ODE"""
        cur_hp = get_pos(self.hp, pos)

        if isinstance(cur_hp, hcsp.Skip):
            pass

        elif isinstance(cur_hp, hcsp.Assign):
            if not isinstance(cur_hp.var_name, expr.AVar):
                raise NotImplementedError
            self.variable_names.add(cur_hp.var_name.name)

        elif isinstance(cur_hp, hcsp.RandomAssign):
            if not isinstance(cur_hp.var_name, expr.AVar):
                raise NotImplementedError
            self.variable_names.add(cur_hp.var_name.name)

        elif isinstance(cur_hp, hcsp.IChoice):
            for i in range(len(cur_hp.hps)):
                sub_pos = pos + (i,)
                self.compute_variable_set(pos=sub_pos)

        elif isinstance(cur_hp, hcsp.Sequence):
            for i in range(len(cur_hp.hps)):
                sub_pos = pos + (i,)
                self.compute_variable_set(pos=sub_pos)

        elif isinstance(cur_hp, hcsp.Loop):
            sub_pos = pos + (0,)
            self.compute_variable_set(pos=sub_pos)

        elif isinstance(cur_hp, hcsp.ODE):
            for name, _ in cur_hp.eqs:
                self.variable_names.add(name)

        elif isinstance(cur_hp, hcsp.ITE):
            for i in range(len(cur_hp.if_hps) + (0 if cur_hp.else_hp is None else 1)):
                sub_pos = pos + (i,)
                self.compute_variable_set(sub_pos)

    def compute_branch_label(self, cur_branch=None, old_blabel=None, blabel_depth=None):
        """Compute the branch label for the weakest precondition.
        {P} c {Q}, P is the wp computed by c and Q.

        type: the type of the hcsp program, i.e. c.
        cur_branch: the branch index of current branch point, acquired in IChoice, ITE, ODE.
            Example, {P1, P2} c1 ++ c2 {Q}, P1 is computed from c1, P2 is computed from c2,
            then the cur_branch for P1 is 1, the cur_branch for P2 is 2.
        old_blabel: the branch label of the weakest precondition of sub-hcsp program below
            the current point, acquired in IChoice, ITE, Sequence.
        blabel_depth: The depth that the labels are currently extended at
        """

        if blabel_depth == 0:
            assert isinstance(old_blabel, label.SequenceLabel) or old_blabel is None
            return label.SequenceLabel(label.AtomLabel(cur_branch), old_blabel)
        else:
            assert isinstance(old_blabel, label.SequenceLabel)
            first_label = old_blabel.labels[0]
            rest_labels = old_blabel.labels[1:]
            if isinstance(first_label, label.NestLabel):
                sublabel = first_label.sub_label
            else:
                sublabel = None
            extended_first_label = self.compute_branch_label(cur_branch, sublabel, blabel_depth - 1)
            return label.SequenceLabel(label.NestLabel(first_label.value, extended_first_label), *rest_labels)


    def add_vc_assume(self, pos):
        # Add assume into the hypothesis of every verification condition.
        if self.infos[pos].assume:
            assume = expr.list_conj(*[sub_assume.expr for sub_assume in self.infos[pos].assume])
            asm_inv_origins = []
            for sub_assume in self.infos[pos].assume:
                asm_inv_origins.extend(sub_assume.origins)
            
            for i in range(len(self.infos[pos].vcs)):
                vc = self.infos[pos].vcs[i]
                self.infos[pos].vcs[i] = Condition(
                    expr=expr.imp(assume, vc.expr), 
                    path=vc.path,
                    blabel=vc.blabel,
                    origins=vc.origins + asm_inv_origins,
                    bottom_loc=vc.bottom_loc, 
                    categ=vc.categ,
                    isVC=True
                    )

    def compute_wp(self, *, pos=((),())):
        """Compute weakest-preconditions using the given information."""

        # Obtain the hp at the given position
        cur_hp = get_pos(self.hp, pos[0])
        type = cur_hp.type

        # The post-condition at the given position should already be
        # available.
        # assert pos in self.infos and self.infos[pos].post is not None
        post = self.infos[pos].post

        if isinstance(cur_hp, hcsp.Skip):
            # Skip: {P} skip {P}
            pre = [Condition(
                expr=subpost.expr, 
                path=subpost.path + [pos],
                origins=subpost.origins,
                blabel_depth=subpost.blabel_depth,
                blabel=subpost.blabel,
                bottom_loc=subpost.bottom_loc, 
                categ=subpost.categ
                ) for subpost in post]
        
        elif isinstance(cur_hp, hcsp.Assign):
            # Assign: {P[e/v]} v := e {P}
            # Compute pre-condition by replacing var_name by expr in the
            # post-condition.
            if not isinstance(cur_hp.var_name, expr.AVar):
                raise NotImplementedError
            if cur_hp.var_name.name in self.constant_names:
                raise NotImplementedError("Constants can not be assigned")

            var = cur_hp.var_name.name
            pre = [Condition(
                expr=subpost.expr.subst({var: cur_hp.expr}), 
                path=subpost.path + [pos],
                origins=subpost.origins,
                blabel_depth=subpost.blabel_depth,
                blabel=subpost.blabel,
                bottom_loc=subpost.bottom_loc,
                categ=subpost.categ
                ) for subpost in post]
        
        elif isinstance(cur_hp, hcsp.RandomAssign):
            # RandomAssign: replace var_name by var_name_new in post and in cur_hp.expr
            #               pre: cur_hp.expr(newvar/var_name) -> post(newvar/var_name)
            # {(v >= e)[v0/v] -> Q[v0/v]} v := {v >= e} {Q}
            if not isinstance(cur_hp.var_name, expr.AVar):
                raise NotImplementedError
            if cur_hp.var_name.name in self.constant_names:
                raise NotImplementedError("Constants can not be assigned: {}".format(cur_hp))

            var_str = cur_hp.var_name.name

            # Create a new var
            newvar = create_newvar(var_str, self.names)
            self.names.add(newvar.name)

            #Compute the pre: hp.expr(newvar|var) -> post(newvar|var)
            pre = [Condition(
                expr=expr.imp(cur_hp.expr.subst({var_str: newvar}), subpost.expr.subst({var_str: newvar})), 
                path=subpost.path + [pos],
                origins=subpost.origins,
                blabel_depth=subpost.blabel_depth,
                blabel=subpost.blabel,
                bottom_loc=subpost.bottom_loc,
                categ=subpost.categ
                ) for subpost in post]

        elif isinstance(cur_hp, hcsp.IChoice):
            # IChoice: 
            #   {P1} c1 {Q}    {P2} c2 {Q}
            # ------------------------------
            #     {P1 && P2} c1 ++ c2 {Q}
            # Pre-condition is the conjunction of the two pre-conditions
            # of subprograms.

            pre = []
            for i in range(len(cur_hp.hps)):
                sub_pos = (pos[0]+(i,), pos[1])
                if sub_pos not in self.infos:
                    self.infos[sub_pos] = CmdInfo()
                sub_info = self.infos[sub_pos]
                sub_info.post = [Condition(
                    expr=subpost.expr,
                    path=subpost.path,
                    origins=subpost.origins,
                    blabel=self.compute_branch_label(cur_branch=i+1, 
                                                     old_blabel=subpost.blabel,
                                                     blabel_depth=subpost.blabel_depth),
                    blabel_depth=subpost.blabel_depth+1,
                    bottom_loc=subpost.bottom_loc,
                    categ=subpost.categ
                    ) for subpost in post]
                sub_info.assume += self.infos[pos].assume
                sub_info.parent_type = cur_hp.type

                self.compute_wp(pos=sub_pos)

                pre += [Condition(
                    expr=subpre.expr, 
                    path=subpre.path,
                    origins=subpre.origins,
                    blabel_depth=max(0,subpre.blabel_depth-1),
                    blabel=subpre.blabel,
                    bottom_loc=subpre.bottom_loc, 
                    categ=subpre.categ
                    ) 
                    for subpre in sub_info.pre]

        elif isinstance(cur_hp, hcsp.ITE):
            # ITE, if b then c1 else c2 endif
            #                       {P1} c1 {Q}  {P2} c2 {Q}  {P3} c3 {Q}
            #-----------------------------------------------------------------------------
            #              {(b1 -> P1) && (!b1 && b2 -> P2)&& (!b1 && !b2 -> P3)} 
            #                      if b1 then c1 elif b2 then c2 else c3 endif 
            #                                         {Q}
            if_hps = cur_hp.if_hps

            sub_imp = []
            if_cond_list = []
            for i in range(len(if_hps) + 1):
                sub_pos = (pos[0] + (i,), pos[1])
                if sub_pos not in self.infos:
                    self.infos[sub_pos] = CmdInfo()
                self.infos[sub_pos].post = [Condition(
                    expr=subpost.expr,
                    path=subpost.path,
                    origins=subpost.origins,
                    blabel=self.compute_branch_label(cur_branch=i+1, 
                                                     old_blabel=subpost.blabel,
                                                     blabel_depth=subpost.blabel_depth),
                    blabel_depth=subpost.blabel_depth+1,
                    bottom_loc=subpost.bottom_loc,
                    categ=subpost.categ
                    ) for subpost in post]
                self.infos[sub_pos].assume += self.infos[pos].assume
                self.infos[sub_pos].parent_type = cur_hp.type

                if i == len(if_hps) and cur_hp.else_hp is None:
                    sub_pre = self.infos[sub_pos].post
                else:
                    # Compute the sub-pre-condition for each sub_hp, 
                    # e.g. P1, P2, P3 for c1, c2 and c3
                    self.compute_wp(pos=sub_pos)
                    sub_pre = self.infos[sub_pos].pre

                # Collect the all if conditions.
                if i < len(if_hps):
                    if_cond_list.append(if_hps[i][0])

                # Compute the hypothesis of each implication
                if i == 0:
                    sub_cond = if_cond_list[0]
                elif i < len(if_hps):
                    sub_cond = expr.LogicExpr('&&', expr.neg_expr(expr.list_disj(*if_cond_list[:i])), if_cond_list[i])
                else:
                    sub_cond = expr.neg_expr(expr.list_disj(*if_cond_list[:]))

                # Compute the implicaiton for each if_hp or else_hp
                for subpre in sub_pre:
                    sub_imp.append(
                        Condition(expr=expr.imp(sub_cond, subpre.expr), 
                            path=subpre.path,
                            origins=subpre.origins,
                            blabel=subpre.blabel,
                            blabel_depth=max(0,subpre.blabel_depth-1),
                            bottom_loc=subpre.bottom_loc,
                            categ=subpre.categ
                            ))

            pre = sub_imp

        elif isinstance(cur_hp, hcsp.Sequence):
            # Sequence of several commands, apply compute_wp from bottom to top
            cur_post = post
            
            for i in reversed(range(len(cur_hp.hps))):
                sub_pos = (pos[0] + (i,), pos[1])
                if sub_pos not in self.infos:
                    self.infos[sub_pos] = CmdInfo()
                sub_info = self.infos[sub_pos]
                sub_info.post = cur_post
                sub_info.assume += self.infos[pos].assume
                sub_info.parent_type = cur_hp.type

                self.compute_wp(pos=sub_pos)
                cur_post = sub_info.pre
            pre = cur_post
            pre = [Condition(expr=subpre.expr, 
                    path=subpre.path,
                    origins=subpre.origins,
                    blabel=subpre.blabel,
                    blabel_depth=subpre.blabel_depth,
                    bottom_loc=subpre.bottom_loc, 
                    categ=subpre.categ
                    ) for subpre in pre]

        elif isinstance(cur_hp, hcsp.Loop):
            # Loop, currently use the invariant that users offered.
            #       {I} c {I}       I -> Q
            # -----------------------------------------
            #              {I} (c)* {Q}

            if cur_hp.constraint != expr.true_expr:
                raise NotImplementedError

            if cur_hp.inv is None:
                raise AssertionError("Loop invariant at position %s is not set." % str(pos))

            # for sub_inv in cur_hp.inv:
            #     if isinstance(sub_inv.expr, expr.LogicExpr):
            #         raise NotImplementedError("Logic expression should be split into several relational expressions")

            all_invs = [sub_inv.expr for sub_inv in cur_hp.inv]

            # One verification condition is I -> Q.
            for i, subpost in enumerate(post):
                self.infos[pos].vcs.append(
                    Condition(expr=expr.imp(expr.list_conj(*all_invs), subpost.expr), 
                                        path=subpost.path,
                                        blabel=subpost.blabel,
                                        origins=subpost.origins + [OriginLoc(index=i, isInv=True, hp_pos=pos[0]) for i in range(len(cur_hp.inv))],
                                        bottom_loc=subpost.bottom_loc,
                                        categ=subpost.categ,
                                        isVC=True
                                        ))

            # Maintain the invariant: {I} c {I}
            body_pos = (pos[0] + (0,), pos[1])
            if body_pos not in self.infos:
                self.infos[body_pos] = CmdInfo()
            body_info = self.infos[body_pos]
            body_info.post = [Condition(expr=sub_inv.expr,
                                        origins=[OriginLoc(index=i, isInv=True, hp_pos=pos[0])],
                                        bottom_loc=OriginLoc(index=i, isInv=True, hp_pos=pos[0]),
                                        categ="maintain")
                                for i, sub_inv in enumerate(cur_hp.inv)]
            body_info.pre = [Condition(expr=sub_inv.expr, 
                                       origins=[OriginLoc(index=i, isInv=True, hp_pos=pos[0])],
                                       bottom_loc=OriginLoc(index=i, isInv=True, hp_pos=pos[0]))
                                for i, sub_inv in enumerate(cur_hp.inv)]
            body_info.assume += self.infos[pos].assume

            self.compute_wp(pos=body_pos)

            
            # Initialize the invariant
            pre = [Condition(expr=sub_inv.expr, 
                             origins=[OriginLoc(index=i, isInv=True, hp_pos=pos[0])],
                             bottom_loc=OriginLoc(index=i, isInv=True, hp_pos=pos[0]), 
                             categ="init") \
                    for i, sub_inv in enumerate(cur_hp.inv)]


        # Reconstruct ODE
        # Only Cut invariant
        elif isinstance(cur_hp, hcsp.ODE):
            # Currently assume out_hp is Skip.
            constraint = cur_hp.constraint
            if cur_hp.out_hp != hcsp.Skip():
                    raise NotImplementedError
            for name, _ in cur_hp.eqs:
                if name in self.constant_names:
                    raise NotImplementedError("Constants cannot be changed in ODEs!")

            if not constraint_examination(constraint):
                raise AssertionError("Constriant is supposed to be open intervals!")

            # Construct dictionary corresponding to eqs.
            if not self.infos[pos].eqs_dict:
                for name, deriv in cur_hp.eqs:
                    self.infos[pos].eqs_dict[name] = deriv

            if cur_hp.rule == "dw":

                # ODE, use differential weakening rule first to prove the hoare triple, 
                # then use other rules to prove invariant.
    
                # The pre-condition for dw rule is set as None initially.
                pre_dw = None
                ghost_vars = []
 
                # TODO: also run if no invariants are specified? testVerify62 testVerify54 testVerify53 testVerify52 testVerify50 testVerify55
                if cur_hp.inv is None:
                    cur_hp.inv = (assertion.CutInvariant(expr=expr.true_expr, proof_methods=None),)

                assert all(isinstance(inv, assertion.CutInvariant) for inv in cur_hp.inv)
                inv_exprs = [inv.expr for inv in cur_hp.inv]
                inv_conj = expr.conj(*inv_exprs)

                # Add ghosts
                # [[bar of D]] <x_dot = e, y_dot = f(x, y)> [[I]]    I && Boundary of D -> Q
                # ----------------------------------------------------------------------------
                #           {(D -> \exists y I) && (!D -> Q)} <x_dot = e & D> {Q}
                # y is a fresh variable, not occurring in <x_dot = e & D> and Q. f(x, y) satisfies
                # Lipschitz condition.
                if cur_hp.ghosts:
                    for ghost in cur_hp.ghosts:
                        # Verify the reasonablity of ghost equations.
                        # f(x, y) should be in the form: a(x) * y + b(x), y is not in a(x) or b(x)
                        ghost_var_degree = degree(sympify(str(ghost.diff).replace('^', '**')), gen=symbols(ghost.var))
                        if not ghost_var_degree in {0,1}:
                            raise AssertionError("Ghost equations should be linear in ghost variable!")
                        self.infos[pos].eqs_dict[ghost.var] = ghost.diff
                        ghost_vars.append(ghost.var)
                    exists_inv = expr.ExistsExpr(ghost_vars, inv_conj)
                    init_cond = [Condition(expr=expr.imp(constraint, exists_inv), 
                                            origins=[OriginLoc(index=i, isInv=True, hp_pos=pos[0])
                                                    for i in range(len(cur_hp.inv))] + 
                                                    [OriginLoc(index=i, isGhost=True, hp_pos=pos[0])
                                                    for i in range(len(cur_hp.ghosts))] + 
                                                    [OriginLoc(isConstraint=True, hp_pos=pos[0])],
                                            categ="init_all",
                                            bottom_loc=OriginLoc(index=len(cur_hp.inv)-1, isInv=True, hp_pos=pos[0]),
                                )]
                    
                # Apply differential weakening (dW)

                # dW Rule (always applied automatically)
                #   [[bar of D]] <x_dot = f(x)> [[I]]      I && Boundary of D -> Q  
                #-----------------------------------------------------------------------
                #           {(D -> I) && (!D -> Q)} <x_dot = f(x) & D> {Q}
                
                # dWT: Case when no invariant is offered(I is set as true)
                #                 Boundary of D -> Q  
                #-----------------------------------------------------------------------
                #           {!D -> Q} <x_dot = f(x) & D> {Q}
                else:
                    init_cond = [Condition(expr=expr.imp(constraint, inv.expr), 
                                    origins=[OriginLoc(index=i, isInv=True, hp_pos=pos[0]), 
                                                OriginLoc(isConstraint=True, hp_pos=pos[0])],
                                    categ="init",
                                    bottom_loc=OriginLoc(index=i, isInv=True, hp_pos=pos[0]),
                        ) for i, inv in enumerate(cur_hp.inv) if inv.expr is not expr.true_expr]

                pre_dw = init_cond \
                        + \
                            [Condition(expr=expr.imp(expr.neg_expr(constraint), 
                                                        subpost.expr),
                                    path=subpost.path,
                                    blabel=self.compute_branch_label(cur_branch='skip', old_blabel=subpost.blabel, blabel_depth=subpost.blabel_depth),
                                    blabel_depth=subpost.blabel_depth,
                                    origins=subpost.origins + [OriginLoc(isConstraint=True, hp_pos=pos[0])],
                                    bottom_loc=subpost.bottom_loc,
                                    categ=subpost.categ
                                    )
                            for subpost in post]
                boundary = compute_boundary(constraint)

                # When I is false_expr, (I && Boundary of D -> Q) is true_expr, which can be omitted. 
                if inv_conj is not expr.false_expr:
                    for subpost in post:
                        e = expr.imp(expr.conj(inv_conj, boundary), subpost.expr)
                        self.infos[pos].vcs.append(
                            Condition(
                                expr=e, 
                                path=subpost.path,
                                blabel=self.compute_branch_label(cur_branch='exec', old_blabel=subpost.blabel, blabel_depth=subpost.blabel_depth),
                                categ=subpost.categ,
                                origins=subpost.origins + 
                                [OriginLoc(index=i, isInv=True, hp_pos=pos[0]) for i in range(len(cur_hp.inv))] + [OriginLoc(isConstraint=True, hp_pos=pos[0])],
                                bottom_loc=subpost.bottom_loc,
                                isVC=True
                                ))
                invs = []
                for i, inv in enumerate(cur_hp.inv):
                    sub_pos = (pos[0], pos[1] + (i,))
                    if sub_pos not in self.infos:
                        self.infos[sub_pos] = CmdInfo()

                    self.infos[sub_pos].assume = self.infos[pos].assume + invs[:i]
                    self.infos[sub_pos].eqs_dict = self.infos[pos].eqs_dict
                    self.infos[sub_pos].inv = Condition(expr=inv.expr, 
                                                origins=[OriginLoc(index=i, isInv=True, hp_pos=pos[0])], 
                                                bottom_loc=OriginLoc(index=i, isInv=True, hp_pos=pos[0]))
                    invs.append(self.infos[sub_pos].inv)
                    self.infos[sub_pos].post = [Condition(expr=inv.expr, 
                                                origins=[OriginLoc(index=i, isInv=True, hp_pos=pos[0])], 
                                                bottom_loc=OriginLoc(index=i, isInv=True, hp_pos=pos[0]))]


                    inv_origin = [OriginLoc(index=i, isInv=True, hp_pos=pos[0])]

                    inv_vars = inv.expr.get_vars()
                    ghost_origins = [OriginLoc(index=idx, isGhost=True, hp_pos=pos[0]) \
                        for idx, var in enumerate(ghost_vars) if var in inv_vars]
        
                    origins = inv_origin + ghost_origins
                    # Invariant triple trivally holds 
                    if inv.rule is None and inv.expr in (expr.true_expr, expr.false_expr):
                        assert inv.rule_arg is None
                    
                    # Use dI rule
                    elif inv.rule == "di" or \
                    (inv.rule is None and inv.expr not in (expr.true_expr, expr.false_expr)):
                        assert inv.rule_arg is None

                        dI_inv = self.infos[sub_pos].inv.expr          
                        # Compute the differential of inv.
                        # One semi-verification condition is closure of constraint -> differential of inv.
                        # (closure of constraint is not necessary because the differential is always a closed set.)
                        differential = compute_diff(dI_inv, eqs_dict=self.infos[sub_pos].eqs_dict, functions=self.functions)
                        closureD = compute_closed_set(constraint)
                        vc = expr.imp(closureD, differential)
            
                        self.infos[sub_pos].vcs.append(Condition(expr=vc, 
                                                            path=[sub_pos],
                                                            origins=origins,
                                                            categ="maintain", 
                                                            bottom_loc=self.infos[sub_pos].inv.bottom_loc,
                                                            isVC=True))
                    # Use dbx rule
                    # Cases when dbx_inv is "e == 0".
                        # Use Darboux Equality Rule
                        #    closure of D -> e_lie_deriv == g * e
                        #--------------------------------------------    (g is the cofactor)
                        #   {e == 0} <x_dot = f(x) & D> {e == 0}
                    # Cases when dbx_inv is e >(>=) 0.
                        # Use Darboux Inequality Rule.
                        #     closure of D -> e_lie_deriv >= g * e
                        # ---------------------------------------------
                        #    e >(>=) 0 <x_dot = f(x) & D> e >(>=) 0
                    elif inv.rule == "dbx":
                        if inv.rule_arg is not None:
                            self.infos[sub_pos].dbx_cofactor = inv.rule_arg

                        dbx_inv = self.infos[sub_pos].inv.expr
                        bottom_loc = self.infos[sub_pos].inv.bottom_loc

                        # For example, simplify !(x > 1) to x <= 1
                        if isinstance(dbx_inv, expr.LogicExpr): 
                            dbx_inv = self.simplify_expression(dbx_inv)
                        
                        assert isinstance(dbx_inv, expr.RelExpr) and \
                            dbx_inv.op in {'==', '>', '>=', '<', '<='}, \
                            print("The wrong type of %s is %s" %(dbx_inv, type(dbx_inv)))

                        # Tranlate '<' and '<=' into '>' and '>='.
                        if dbx_inv.op == '<':
                            dbx_inv = expr.RelExpr('>', dbx_inv.expr2, dbx_inv.expr1)
                        elif dbx_inv.op == '<=':
                            dbx_inv = expr.RelExpr('>=', dbx_inv.expr2, dbx_inv.expr1)
                        # Translate into the form e == 0 or e >(>=) 0
                        if dbx_inv.expr2 != expr.AConst(0):
                            expr1 =  expr.OpExpr('-', dbx_inv.expr1, dbx_inv.expr2)
                            expr1 = self.simplify_expression(expr1)
                            dbx_inv = expr.RelExpr(dbx_inv.op, expr1, expr.AConst(0)) 
                        
                        e = dbx_inv.expr1
                        assert self.is_polynomial(e, self.constant_names) is True
                        # Compute the lie derivative of e.
                        e_lie_deriv = compute_diff(e, eqs_dict=self.infos[sub_pos].eqs_dict, functions=self.functions)             

                        # Cases when dbx_inv is "e == 0".
                        # Use Darboux Equality Rule
                        #          D -> e_lie_deriv == g * e
                        #--------------------------------------------    (g is the cofactor)
                        #   {e == 0} <x_dot = f(x) & D> {e == 0}
                        if dbx_inv.op == "==" :

                            # Case when the cofactor g is not offered.
                            # Compute the cofactor g by auto.
                            if self.infos[sub_pos].dbx_cofactor is None:
                                g = expr.OpExpr('/', e_lie_deriv, e)
                                g = self.simplify_expression(g)

                                assert self.is_polynomial(g, self.constant_names) is True
                                self.infos[sub_pos].dbx_cofactor = g

                            # Case when cofactor g is offered by the user.
                            else:
                                g = self.infos[sub_pos].dbx_cofactor
                                assert self.is_polynomial(g, self.constant_names) is True

                                # closure of D -> e_lie_deriv == g * e
                                # (closure of D is not necessary because "e_lie_deriv == g * e" is a closed set)
                                closureD = compute_closed_set(constraint)
                                vc = expr.imp(closureD, expr.RelExpr('==', e_lie_deriv, 
                                                                            expr.OpExpr('*', g, e)))

                                self.infos[sub_pos].vcs.append(Condition(
                                                                expr=vc, 
                                                                path=[sub_pos],
                                                                origins=origins, 
                                                                bottom_loc=bottom_loc,
                                                                categ="maintain", 
                                                                isVC=True))

                        # Cases when dbx_inv is e >(>=) 0.
                        # Use Darboux Inequality Rule.
                        #     closure of D -> e_lie_deriv >= g * e
                        # ---------------------------------------------
                        #    e >(>=) 0 <x_dot = f(x) & D> e >(>=) 0
                        elif dbx_inv.op in {'>', '>='}:
                            # Cases when the cofactor g is not offered.
                            # Compute the cofactor automatically.
                            if self.infos[sub_pos].dbx_cofactor is None:
                                quot_remains = self.polynomial_div(e_lie_deriv, e, self.constant_names)
                                
                                # Several quot and remain pairs may returned from the polynomial division.
                                # If there is a remain >= 0, there exists a quot satisfying g in dbx_rule.
                                vc_comps = []
                                for _, remain in quot_remains.items():
                                    # remain (e_lie_deriv - g * e) >= 0.
                                    vc_comp = expr.RelExpr('>=', remain, expr.AConst(0))
                                    vc_comps.append(vc_comp)
                                closureD = compute_closed_set(constraint)
                                vc = expr.imp(closureD, expr.list_disj(*vc_comps))

                                self.infos[sub_pos].vcs.append(Condition(
                                                                expr=vc,
                                                                path=[sub_pos], 
                                                                origins=origins, 
                                                                categ="maintain",
                                                                bottom_loc=bottom_loc, 
                                                                isVC=True))

                            # Cases when the cofactor g is offered by the user.
                            else:
                                g = self.infos[sub_pos].dbx_cofactor
                                assert self.is_polynomial(g, self.constant_names) is True
                                
                                closureD = compute_closed_set(constraint)
                                vc = expr.imp(closureD, expr.RelExpr('>=', e_lie_deriv, 
                                                                            expr.OpExpr('*', self.infos[sub_pos].dbx_cofactor, e)))
                                self.infos[sub_pos].vcs.append(Condition(
                                                                expr=vc,
                                                                path=[sub_pos], 
                                                                origins=origins, 
                                                                categ="maintain", 
                                                                bottom_loc=bottom_loc, isVC=True))

                    # Use barrier certificate
                    #      closure of D && e == 0 -> e_lie > 0
                    # --------------------------------------------------
                    #      {e >=(>) 0} <x_dot = f(x) & D> {e >=(>) 0}                        
                    elif inv.rule == "bc":
                        assert inv.rule_arg is None

                        barrier_inv = self.infos[sub_pos].inv.expr
                        bottom_loc = self.infos[sub_pos].inv.bottom_loc
                        origins = self.infos[sub_pos].inv.origins

                        if isinstance(barrier_inv, expr.LogicExpr):
                            barrier_inv = self.simplify_expression(barrier_inv)

                        assert isinstance(barrier_inv, expr.RelExpr) and \
                            barrier_inv.op in {'<=', '>=', '>', '<'}

                        # TODO: e should be continous

                        # Translate '<=' into '>='
                        if barrier_inv.op == '<=':
                            barrier_inv = expr.RelExpr('>=', barrier_inv.expr2, barrier_inv.expr1)
                        elif barrier_inv.op == '<':
                            barrier_inv = expr.RelExpr('>', barrier_inv.expr2, barrier_inv.expr1)

                        # Translate 'e >= c' into 'e - c >= 0'
                        if barrier_inv.expr2 != 0:
                            expr1 = expr.OpExpr('-', barrier_inv.expr1, barrier_inv.expr2)
                            # expr1 = self.simplify_expression(expr1)
                            barrier_inv = expr.RelExpr(barrier_inv.op, expr1, expr.AConst(0))

                        e = barrier_inv.expr1
                        e_lie = compute_diff(e, eqs_dict=self.infos[sub_pos].eqs_dict, functions=self.functions)

                        # vc: closure of D && e == 0 -> e_lie > 0
                        closureD = compute_closed_set(constraint)
                        vc = expr.imp(expr.LogicExpr('&&', closureD, 
                                                        expr.RelExpr('==', e, expr.AConst(0))),
                                    expr.RelExpr('>', e_lie, expr.AConst(0)))

                        self.infos[sub_pos].vcs.append(Condition(
                            expr=vc, 
                            path=[sub_pos], 
                            origins=origins, 
                            categ="maintain", 
                            bottom_loc=bottom_loc, 
                            isVC=True))
   
                    else:
                        if inv.rule is not None:
                            raise NotImplementedError("Unknown ODE method")

                    # Add the assume into the hypothesis of every verification condition at sub_pos.
                    self.add_vc_assume(sub_pos)
             
                pre = pre_dw
                
            elif cur_hp.rule == "solution":
                # P' = \forall t > 0. (\forall 0 <= s < t. D(u(s))) && !D(u(t)) -> Q(u(t))
                # 
                # -----------------------------------------------------
                #    {(D -> P') && (!D -> Q)} <x_dot = f(x) & D(x)> {Q}
                # f(x) is linear in x. Assume u(.) solve the symbolic initial value problem u'(t) = f(u), u(0) = x
                for var, diff in self.infos[pos].eqs_dict.items():
                            d = degree(sympify(str(diff).replace('^', '**')), gen=symbols(var))
                            if not d in {0,1}:
                                raise AssertionError("{0} should be linear in {1} when using sln rule!".format(diff, var))

                # Create a new variable to represent time
                time_var = create_newvar('t', self.names)

                # Solution is, e.g. {'x' : x + v*t + a*t^2/2, 'v' : v + a*t}.
                solution_dict = solveODE(cur_hp, self.names, time_var.name)

                # Create a new variable to represent 's' in 'ForAll 0 <= s < t'
                in_var = create_newvar('s', self.names)
                self.names.add(in_var.name)

                # Compute u_s, alias u(s)
                # e.g. {'x' : x + v*s + a*s^2/2, 'v' : v + a*s
                u_s = dict()
                for fun_name, sol in solution_dict.items():
                    sol_s = sol.subst({time_var.name : in_var})
                    u_s[fun_name] = sol_s

                D_u_s = constraint.subst(u_s)
                D_u_t = constraint.subst(solution_dict)

                pre = []
                for subpost in post:
                    Q_u_t = subpost.expr.subst(solution_dict)

                    # Compute the hypothesis of implication
                    # \forall 0 <= s < t D(u(s)) && !D(u(t))
                    subcond = expr.ForAllExpr(in_var.name, 
                                expr.imp(expr.LogicExpr('&&', 
                                                        expr.RelExpr('<=', expr.AConst(0), in_var),
                                                        expr.RelExpr('<', in_var, time_var)),
                                         D_u_s))
                    cond = expr.LogicExpr('&&', 
                                subcond,
                                expr.LogicExpr('!', D_u_t))

                    # Compute the conclusion of implication
                    conclu = Q_u_t

                    # Compute P'
                    pre_expr = expr.ForAllExpr(time_var.name,
                                               expr.imp(expr.RelExpr('>', time_var, expr.AConst(0)),
                                                        expr.imp(cond, conclu)))

                    pre_exec = Condition(expr=pre_expr,
                                         path=subpost.path + [pos],
                                         blabel=self.compute_branch_label(cur_branch='exec',
                                                old_blabel=subpost.blabel, blabel_depth=subpost.blabel_depth),
                                         blabel_depth=subpost.blabel_depth,
                                         origins=subpost.origins,
                                         bottom_loc=subpost.bottom_loc,
                                         categ=subpost.categ)
                    pre_skip = Condition(expr=expr.imp(expr.neg_expr(constraint), 
                                                        subpost.expr),
                                        path=subpost.path,
                                        blabel=self.compute_branch_label(cur_branch='skip', 
                                            old_blabel=subpost.blabel, blabel_depth=subpost.blabel_depth),
                                        blabel_depth=subpost.blabel_depth,
                                        origins=subpost.origins + [OriginLoc(isConstraint=True, hp_pos=pos[0])],
                                        bottom_loc=subpost.bottom_loc,
                                        categ=subpost.categ
                                        )
                                    
                    pre = pre + [pre_exec, pre_skip]

            else:
                raise NotImplementedError

        else:
            raise NotImplementedError

        # Assign pre-condition, or create a new verification condition if the
        # pre-condition is already set.
        if self.infos[pos].pre is None:
            self.infos[pos].pre = pre
        else:
            # self.infos[pos].pre is the pre-condition of the whole hp.
            pre_conj = expr.conj(*[subpre.expr for subpre in self.infos[pos].pre])
            subpre_origins = []
            for subpre in self.infos[pos].pre:
                subpre_origins.extend(subpre.origins)
            for i, vc in enumerate(pre):
                self.infos[pos].vcs.append(
                    Condition(expr=expr.imp(pre_conj, vc.expr), 
                              path=vc.path,
                              blabel=vc.blabel, 
                              origins=vc.origins + subpre_origins,
                              bottom_loc=vc.bottom_loc, 
                              categ=vc.categ,
                              isVC=True
                              ))

        # Add assume into the hypothesis of every verification condition at pos.
        self.add_vc_assume(pos)
        
    def convert_imp(self, e):
        """Convert implication from (p -> q -> u) to (p && q) -> u,
        in which the right expression won't be an implication """
        if isinstance(e, expr.LogicExpr) and e.op == '->':
            if isinstance(e.exprs[1], expr.LogicExpr) and e.exprs[1].op == '->':
                l_expr = expr.LogicExpr('&&', e.exprs[0], e.exprs[1].exprs[0])
                r_expr = e.exprs[1].exprs[1]
                return self.convert_imp(expr.imp(l_expr, r_expr))
            # p -> q
            else:
                return e
        else:
            return e
 
    def set_solver(self, vc):
        """Set the solver of verification condition, which is z3 by default, as the one indicated in  proof method"""
        assert isinstance(vc, Condition) and vc.isVC is True
        assert vc.bottom_loc is not None

        isPost = vc.bottom_loc.isPost

        # Proof method of each vc is stored in the bottom-most assertion related.

        if isPost:
            assertion = self.post[vc.bottom_loc.index]
        
        else:
            assert vc.bottom_loc.hp_pos is not None
            bottom_hp = get_pos(self.hp, vc.bottom_loc.hp_pos)

            assert isinstance(bottom_hp, (hcsp.Loop, hcsp.ODE))
            assertion = bottom_hp.inv[vc.bottom_loc.index]

        # Match the computed label of vc and the one in proof method.
        for pms in assertion.proof_methods.pms:
            if str(vc.comp_label) == str(pms.label):
                vc.solver = pms.method

        return vc

    def get_all_vcs(self):
        all_vcs = dict()
        for pos, info in self.infos.items():   
            if info.vcs:
                all_vcs[pos] = info.vcs
        return all_vcs

    def verify(self):
        """Verify all VCs in self."""
        all_vcs = self.get_all_vcs()
        
        for pos, vcs in all_vcs.items():
            for vc in vcs:
                vc = self.set_solver(vc)
                if not self.verify_vc(vc):
                    print("The failed verification condition is :\n", pos, ':', str(vc))
                    return False
        return True



    def verify_vc(self, vc):
        """Verify one verfication condition with its solver"""
        solver = vc.solver
        if solver == 'wolfram':
            if wl_prove(vc.expr, self.functions):
                return True
            else:
                return False

        elif solver == 'z3':
            if z3_prove(vc.expr, self.functions):
                return True
            else:
                return False

        else:
            raise AssertionError("Please choose an arithmetic solver.")




            


