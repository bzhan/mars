"""
Python implementation of Hybrid Hoare Logic.

This version uses data structures that are separate from the main
HCSP program.

"""
from sympy import sympify, degree, symbols, factor_list, fraction, simplify

from hhlpy.sympy_wrapper import sp_polynomial_div, sp_simplify
from hhlpy.wolframengine_wrapper import solveODE
from hhlpy.wolframengine_wrapper import wl_prove
from hhlpy.wolframengine_wrapper import wl_simplify, wl_polynomial_div
from hhlpy.z3wrapper import z3_prove
from ss2hcsp.hcsp import hcsp, expr
from ss2hcsp.hcsp.parser import aexpr_parser, bexpr_parser
from ss2hcsp.hcsp.simulator import get_pos


def compute_diff(e, eqs_dict):
    """Compute differential of an arithmetic or boolean expression."""
    def rec(e):
        if isinstance(e, expr.LogicExpr):
            if e.op == "&&":
                return expr.LogicExpr("&&", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == "||":
                return expr.LogicExpr("&&", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == "-->":
                return rec(expr.LogicExpr("||", expr.neg_expr(e.exprs[0]), e.exprs[1]))
            elif e.op == "~":
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
        elif isinstance(e, expr.FunExpr):
            if len(e.exprs) == 0:
                return expr.AConst(0)
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
                # d(u/v) = (u*dv + du * v)/ v^2
                # If v is constant, d(u/v) = 1/v * du, which is easier than using above rule.
                if isinstance(e.exprs[1], expr.AConst) or \
                   isinstance(e.exprs[1], expr.FunExpr) and len(e.exprs == 0): # actually a constant
                    du = rec(e.exprs[0])
                    return expr.OpExpr('*', expr.OpExpr('/', expr.AConst(1), e.exprs[1]), du)
                else:
                    du = rec(e.exprs[0])
                    dv = rec(e.exprs[1])
                    numerator = expr.OpExpr("+", expr.OpExpr("*", e.exprs[0], dv), expr.OpExpr("*", du, e.exprs[1]))
                    denominator = expr.OpExpr('*', e.exprs[1], e.exprs[1])
                    return expr.OpExpr('/', numerator, denominator)            
            else:
                raise NotImplementedError
    
    return rec(e)

def constraint_examination(e):
    '''Examine whether the constraint is open intervals or not.'''
    if not isinstance(e, expr.BExpr):
        raise NotImplementedError
    
    def rec(e):
        if isinstance(e, expr.RelExpr):
            if e.op in [">", "<", "!="]:
                return True
            else:
                return False
        elif isinstance(e, expr.LogicExpr):
            if e.op == '~':
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
        elif e.op == '~':
            return compute_boundary(expr.neg_expr(e.exprs[0]))

# Return the relexpression 'denomibator != 0' for term e.           
def demoninator_not_zero(e):
    if not isinstance(e, expr.AExpr):
        raise NotImplementedError

    if not isinstance(e, str):
        e = str(e)
    
    e = simplify(sympify(e.replace('^', '**')))
    _, denominator = fraction(e)
    denominator = aexpr_parser.parse(str(denominator).replace('**', '^'))

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
    suffix_n = 0
    while (s + str(suffix_n) in names):
        suffix_n = suffix_n + 1
    return expr.AVar(s + str(suffix_n))

class CmdInfo:
    """Information associated to each HCSP program."""
    def __init__(self):
        # Pre-condition and post-condition are assertions.
        self.pre = None
        self.post = None
        self.stren_post = None

        # List of verification conditions for this command.
        self.vcs = []

        # Invariants for loops.
        self.loop_inv = None

        # Equation dict for ODEs.
        self.eqs_dict = dict()

        # Assumptions for HCSPs.
        self.assume = []

        # Use solution axiom or not
        self.sln_rule = False

        # Use differential weakening rule or not
        self.dw = False

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

    def __str__(self):
        res = ""
        res += "pre = %s\n" % self.pre
        res += "post = %s\n" % self.post
        if self.stren_post is not None:
            res += "stren = %s \n" % self.stren_post
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


class CmdVerifier:
    """Contains current state of verification of an HCSP program."""
    def __init__(self, *, pre, hp, post, constants=set(), wolfram_engine = False, z3 = True):
        # The HCSP program to be verified.
        self.hp = hp

        # The prover used to verify conditions.
        # Use z3 by default.
        self.wolfram_engine = wolfram_engine
        self.z3 = z3
        if self.wolfram_engine:
            self.z3 = False

        # Mapping from program position to CmdInfo objects.
        self.infos = dict()

        # Set of function names that are used
        funs = hp.get_funs().union(pre.get_funs(), post.get_funs())

        # Set of var_names that are used, the names of AVar expression 
        vars = hp.get_vars().union(pre.get_vars(), post.get_vars())

        # Set of funtion names and varnames that are used
        self.names = funs.union(vars)

        # Set of constants that are appointed
        self.constants = constants

        # Set of program variables that are used
        self.variables = vars - self.constants

        # Initialize info for the root object. Place pre-condition and post-condition.
        # pos is a pair of two tuples. 
        # pos[0] is the position of the sub_hp in hp.
        # pos[1] is the number of subproof of the same sub_hp
        root_pos = ((),())
        self.infos[root_pos] = CmdInfo()
        self.infos[root_pos].pre = pre
        self.infos[root_pos].post = post

        # If there are pre-conditions of constants in the form: A op c, 
        # in which A is a constant symbol, c doesn't include variable symbols, op is in RelExpr.op
        # the pre-conditions will always hold.
        # Add this kind of pre-conditions into assumptions in HCSPs.

        # There are constants in pre.
        if not self.constants.isdisjoint(pre.get_vars().union(pre.get_funs())):
            if isinstance(pre, expr.RelExpr):
                if pre.get_vars().isdisjoint(self.variables):
                    self.infos[root_pos].assume.append(pre)

            elif isinstance(pre, expr.LogicExpr):
                # Assume pre is a conjunction function
                if pre.op == '&&':
                    pre_list = expr.split_conj(pre)
                    for sub_pre in pre_list:
                        # No variables in sub_pre.
                        if sub_pre.get_vars().isdisjoint(self.variables):
                            self.infos[root_pos].assume.append(sub_pre)
                else:
                    raise NotImplementedError

            else:
                raise NotImplementedError

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

    def add_strengthened_post(self, pos, stren_post):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].stren_post = stren_post

    def add_loop_invariant(self, pos, loop_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].loop_inv = loop_inv

    def use_solution_rule(self, pos, sln_rule):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].sln_rule = sln_rule

    def use_diff_weakening_rule(self, pos, dw):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].dw = dw

    def use_diff_invariant_rule(self, pos, dI_rule):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].dI_rule = dI_rule

    def add_dI_invariant(self, pos, dI_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].dI_inv = dI_inv

    def add_diff_cuts(self, pos, diff_cuts):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].diff_cuts = diff_cuts

    def add_ghost_invariant(self, pos, ghost_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].ghost_inv = ghost_inv

    def add_ghost_equation(self, pos, ghost_eqs):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].ghost_eqs = ghost_eqs

    def add_dG_invariant(self, pos, dG_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].dG_inv = dG_inv

    def use_darboux_rule(self, pos, dbx_rule):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].dbx_rule = dbx_rule

    def add_darboux_invariant(self, pos, dbx_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].dbx_inv = dbx_inv

    def add_darboux_cofactor(self, pos, dbx_cofactor):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].dbx_cofactor = dbx_cofactor

    def use_barrier_certificate_rule(self, pos, barrier_rule):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].barrier_rule = barrier_rule

    def add_barrier_invariant(self, pos, barrier_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].barrier_inv = barrier_inv

    def use_conjunction_rule(self, pos, conj_rule):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].conj_rule = conj_rule

    def simplify_expression(self, e):
        if self.wolfram_engine:
            e = wl_simplify(e)

        # Use sympy to simplify
        else:
            e = sp_simplify(e)

        return e

    def polynomial_div(self, p, q):
        """Compute the quotient and remainder of polynomial p and q"""
        if self.wolfram_engine:
            quot_remains = wl_polynomial_div(p, q)
        else:
            quot_remains = sp_polynomial_div(p, q)

        return quot_remains

    def compute_wp(self, *, pos=((),())):
        """Compute weakest-preconditions using the given information."""

        # Obtain the hp at the given position
        cur_hp = get_pos(self.hp, pos[0])

        # The post-condition at the given position should already be
        # available.
        assert pos in self.infos and self.infos[pos].post is not None
        if self.infos[pos].stren_post is not None:
            self.infos[pos].vcs.append(expr.imp(self.infos[pos].stren_post, self.infos[pos].post))
            post = self.infos[pos].stren_post
        else:
            post = self.infos[pos].post

        if isinstance(cur_hp, hcsp.Skip):
            # Skip: {P} skip {P}
            pre = post
        
        elif isinstance(cur_hp, hcsp.Assign):
            # Assign: {P[e/v]} v := e {P}
            # Compute pre-condition by replacing var_name by expr in the
            # post-condition.
            if not isinstance(cur_hp.var_name, expr.AVar):
                raise NotImplementedError
            if cur_hp.var_name in self.constants:
                raise NotImplementedError("Constants can not be assigned")

            var = cur_hp.var_name.name
            pre = post.subst({var: cur_hp.expr})
        
        elif isinstance(cur_hp, hcsp.RandomAssign):
            # RandomAssign: replace var_name by var_name_new in post and in cur_hp.expr
            #               pre: cur_hp.expr(newvar|var_name) --> post(newvar|var_name)
            if not isinstance(cur_hp.var_name, expr.AVar):
                raise NotImplementedError
            if cur_hp.var_name in self.constants:
                raise NotImplementedError("Constants can not be assigned")

            var_str = cur_hp.var_name.name

            # Create a new var
            newvar = create_newvar(var_str, self.names)
            self.names.add(newvar.name)

            #Compute the pre: hp.expr(newvar|var) --> post(newvar|var)
            pre = expr.imp(cur_hp.expr.subst({var_str: newvar}), post.subst({var_str: newvar}))


        elif isinstance(cur_hp, hcsp.IChoice):
            # IChoice: 
            #   {P1} c1 {Q}    {P2} c2 {Q}
            # ------------------------------
            #     {P1 & P2} c1 ++ c2 {Q}
            # Pre-condition is the conjunction of the two pre-conditions
            # of subprograms.

            pos0 = (pos[0]+(0,), pos[1]) 
            pos1 = (pos[0]+(1,), pos[1])
            if pos0 not in self.infos:
                self.infos[pos0] = CmdInfo()
            if pos1 not in self.infos:
                self.infos[pos1] = CmdInfo()
            info1 = self.infos[pos0]
            info2 = self.infos[pos1]
            info1.post = post
            info2.post = post
            info1.assume += self.infos[pos].assume
            info2.assume += self.infos[pos].assume
            self.compute_wp(pos=pos0)
            self.compute_wp(pos=pos1)
            pre = expr.conj(self.infos[pos0].pre, self.infos[pos1].pre)
            # if self.infos[pos].split:
            #     pre = expr.split_conj(pre)
        
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
                self.compute_wp(pos=sub_pos)
                cur_post = sub_info.pre
            pre = cur_post

        elif isinstance(cur_hp, hcsp.Loop):
            # Loop, currently use the invariant that users offered.
            if cur_hp.constraint != expr.true_expr:
                raise NotImplementedError

            if self.infos[pos].loop_inv is None:
                raise AssertionError("Loop invariant at position %s is not set." % str(pos))

            inv = self.infos[pos].loop_inv
            if not isinstance(inv, expr.BExpr):
                raise NotImplementedError('Invalid Invariant for Loop!') 

            # Compute wp for loop body with respect to invariant
            sub_pos = (pos[0] + (0,), pos[1])
            if sub_pos not in self.infos:
                self.infos[sub_pos] = CmdInfo()
            sub_info = self.infos[sub_pos]
            sub_info.post = inv
            sub_info.assume += self.infos[pos].assume
            self.compute_wp(pos=sub_pos)
            pre_loopbody = sub_info.pre

            # pre is also set to be the invariant
            pre = inv

            # The 1st verification condition is invariant --> pre_loopbody.
            # If the pre condition of loop body is a conjunction expression, split it.
            if isinstance(pre_loopbody, expr.LogicExpr) and pre_loopbody.op == '&&':
                sub_pres = expr.split_conj(pre_loopbody)
                self.infos[pos].vcs += list(expr.imp(inv, sub_pre) \
                                                for sub_pre in sub_pres)
            else:
                self.infos[pos].vcs.append(expr.imp(inv, pre_loopbody))

            # The 2nd verification condition is invariant --> post.
            self.infos[pos].vcs.append(expr.imp(inv, post))

        elif isinstance(cur_hp, hcsp.ODE):
            # ODE, use the differential invariant rule, differential cut rule and differential ghost rule.
            # Currently assume out_hp is Skip.
            constraint = cur_hp.constraint

            if cur_hp.out_hp != hcsp.Skip():
                raise NotImplementedError
            for name, _ in cur_hp.eqs:
                if name in self.constants:
                    raise NotImplementedError("Constants cannot be changed in ODEs!")

            if not constraint_examination(constraint):
                raise AssertionError("Constriant is supposed to be open intervals!")

            # Construct dictionary corresponding to eqs.
            if not self.infos[pos].eqs_dict:
                for name, deriv in cur_hp.eqs:
                    self.infos[pos].eqs_dict[name] = deriv

            # Use solution axiom
            # 
            #             P -->
            # ForAll t >= 0  ((ForAll 0 <= s < t D(y(s)) && not D(y(t))) --> (ForAll 0 <= s <= t Q(y(s)))
            #--------------------------------------------------------------------------------------------
            #      {P} <x_dot = f(x) & D(x)> {Q(x)}
            #
            # Assume y(.) solve the symbolic initial value problem y'(t) = f(y), y(0) = x

            if self.infos[pos].sln_rule:

                # Create a new variable to represent time
                time_var = create_newvar('t', self.names)
                self.names.add(time_var.name)

                # Solution is, e.g. {'x' : x + v*t + a*t^2/2, 'v' : v + a*t}.
                solution_dict = solveODE(cur_hp, self.names, time_var.name)

                # Create a new variable to represent 's' in 'ForAll 0 <= s < t'
                in_var = create_newvar('s', self.names)
                self.names.add(in_var.name)

                # Compute y_s, alias y(s)
                # e.g. {'x' : x + v*s + a*s^2/2, 'v' : v + a*s
                y_s = dict()
                for fun_name, sol in solution_dict.items():
                    sol_s = sol.subst({time_var.name : in_var})
                    y_s[fun_name] = sol_s

                D_y_t = constraint.subst(solution_dict)
                D_y_s = constraint.subst(y_s)
                Q_y_s = post.subst(y_s)

                # Compute the hypothesis of implication
                # ForAll (s, 0 <= s < t --> D(y(s)) && not D(y(t))
                sub_cond = expr.ForAllExpr(in_var.name, 
                                expr.imp(expr.LogicExpr('&&', 
                                                        expr.RelExpr('<=', expr.AConst(0), in_var),
                                                        expr.RelExpr('<', in_var, time_var)),
                                         D_y_s))
                cond = expr.LogicExpr('&&', 
                                      sub_cond,
                                      expr.LogicExpr('~', D_y_t))
                # Compute the conclusion of implication
                # ForAll (s, 0 <= s <= t --> Q(y(s))
                conclu = expr.ForAllExpr(in_var.name,
                                expr.imp(expr.LogicExpr('&&', 
                                                        expr.RelExpr('<=', expr.AConst(0), in_var),
                                                        expr.RelExpr('<=', in_var, time_var)),
                                         Q_y_s))

                pre = expr.ForAllExpr(time_var.name,
                            expr.imp(expr.RelExpr('>=', time_var, expr.AConst(0)),
                                    expr.imp(cond, conclu)))                                           
           
            # Use dW rule
            # Note: remain unproved!
            # When dw is True.
            #      P --> (~D --> Q) && (D --> (Boundary of D => Q))
            #-----------------------------------------------------
            #               {P} <x_dot = f(x) & D> {Q}
            elif self.infos[pos].dw:

                boundary = compute_boundary(constraint)
                semi_vc = expr.imp(boundary, post)
                if z3_prove(semi_vc):
                    semi_vc_result = expr.true_expr
                else:
                    semi_vc_result = expr.false_expr

                pre = expr.LogicExpr('&&', expr.imp(expr.neg_expr(constraint), post),
                                           expr.imp(constraint, semi_vc_result))

            # Use dI rules
            # When dI_inv is set or by default
            elif self.infos[pos].dI_inv or self.infos[pos].dI_rule or \
                not self.infos[pos].sln_rule and \
                not self.infos[pos].dw and \
                not self.infos[pos].diff_cuts and \
                not self.infos[pos].ghost_inv and self.infos[pos].dG_inv is None and \
                not self.infos[pos].dbx_rule and \
                   not self.infos[pos].dbx_inv and not self.infos[pos].dbx_cofactor and \
                not self.infos[pos].barrier_rule and not self.infos[pos].barrier_inv and \
                not self.infos[pos].conj_rule:

                # By default, dI_inv is post.
                if self.infos[pos].dI_inv is None:
                    self.infos[pos].dI_inv = post

                dI_inv = self.infos[pos].dI_inv           
                # Compute the differential of inv.
                # Compute the boundary of constraint. 
                # One semi-verification condition is boundary of constraint --> differential of inv.
                differential = compute_diff(dI_inv, eqs_dict=self.infos[pos].eqs_dict)
                vc = expr.imp(constraint, differential)

                self.infos[pos].vcs.append(vc)
                if dI_inv != post:
                    self.infos[pos].vcs.append(expr.imp(dI_inv, post))

                pre = dI_inv

            # Use dC rules
            #            {R1} c {R1}    R1 => {R2} c {R2}   P --> R1 && R2   R1 && R2 --> Q
            #--------------------------------------------------------------------------------
            #                                       {P} c {Q}
            elif self.infos[pos].diff_cuts:
                diff_cuts = self.infos[pos].diff_cuts
                
                # Record the pre of each subproof
                pre_list =[]

                # Compute wp for each subproof, whose post condition is diff_cut.
                for i, diff_cut in enumerate(diff_cuts):
                    
                    # Create CmdInfo for every subproof.
                    sub_pos = (pos[0], pos[1] + (i,))
                    if sub_pos not in self.infos:
                        self.infos[sub_pos] = CmdInfo()

                    # Post condition of the each subproof is diff_cut.
                    self.infos[sub_pos].post = diff_cut
                    #  Diff_cut must be an invariant for ODE (for the sake of being added into assume), so diff_cut cannot use dw rule to verify.
                    assert self.infos[sub_pos].dw is not None

                    # If i == 0, no update for assume, else, assume is updated by adding diff_cuts[:i].
                    if i != 0:
                        self.infos[sub_pos].assume += self.infos[pos].assume + diff_cuts[:i]

                    self.compute_wp(pos=sub_pos)

                    pre_list.append(self.infos[sub_pos].pre)

                # Compute wp for the last branch, in which the post condition is post.
                # sub_pos = (pos[0], pos[1] + (len(diff_cuts),))
                # if sub_pos not in self.infos:
                #     self.infos[sub_pos] = CmdInfo()
                # self.infos[sub_pos].post = post
                # self.infos[sub_pos].assume += self.infos[pos].assume + diff_cuts[:]
                # self.compute_wp(pos=sub_pos)
                # pre_list.append(self.infos[sub_pos].pre)

                dC_inv = expr.list_conj(*diff_cuts)
                self.infos[pos].vcs.append(expr.imp(dC_inv, post))
                pre = expr.list_conj(*pre_list)

            # Use dG rules
            # I <--> EX y. G   {G} <x_dot = f(x), y_dot = a(x) * y + b(x) &D> {G}
            #---------------------------------------------------------------------
            #                   {I} <x_dot = f(x) & D> {I}
            elif self.infos[pos].ghost_inv is not None:
                ghost_inv = self.infos[pos].ghost_inv

                # By default, dG_inv is post.
                if self.infos[pos].dG_inv is None:
                    self.infos[pos].dG_inv = post
                dG_inv = self.infos[pos].dG_inv

                ghost_vars = [v for v in ghost_inv.get_vars() if v not in self.names]
                if len(ghost_vars) != 1:
                    raise AssertionError("Number of ghost variables is not 1.")
                ghost_var = ghost_vars[0]
                self.names.add(ghost_var)

                if not self.infos[pos].eqs_dict:
                    for name, deriv in cur_hp.eqs:
                        self.infos[pos].eqs_dict[name] = deriv

                # The first condition is: dG_inv implies there exists a value of ghost_var
                # that satisfies ghost_inv.
                vc1 = expr.imp(dG_inv, expr.ExistsExpr(ghost_var, ghost_inv))

                # Second condition: 
                # If the differential equation satisfied by the ghost variable is offered, verify its soundness.
                # if not, solve for the ghost equation automatically.
                # Then verify the reasonablity of the ghost eqaution for above two cases.

                # Cases when the differential equation, alias ghost_eqs offered by the users.
                # Assume y is the ghost variable.
                if self.infos[pos].ghost_eqs:
                    ghost_eqs = self.infos[pos].ghost_eqs

                    assert len(ghost_eqs) == 1, 'Number of ghost variables is not 1.' 
                    assert ghost_var in ghost_eqs, \
                        'The ghost variable in ghost equation is different from that in ghost invariant.'
                    
                    # The verification of the reasonablity of the ghost equations is below if-else.
                    dy = ghost_eqs[ghost_var]

                    # Create a new CmdInfo for the ODE with ghost_eqs
                    sub_pos = (pos[0], pos[1] + (0,))

                    if sub_pos not in self.infos:
                        self.infos[sub_pos] = CmdInfo()

                    self.infos[sub_pos].post = ghost_inv

                    # The eqs_dict in sub_pos is eqs_dict in pos with ghost_eqs.
                    if not self.infos[sub_pos].eqs_dict:
                        self.infos[sub_pos].eqs_dict = self.infos[pos].eqs_dict.copy()
                        self.infos[sub_pos].eqs_dict[ghost_var] = ghost_eqs[ghost_var]

                    self.compute_wp(pos=sub_pos)

                # Cases when ghost_eqs is not offered.
                # Solve for ghost_eqs automatically.
                # assume y is the ghost variable, and x are the other variables.
                else:
                    assert isinstance(ghost_inv, expr.RelExpr) and ghost_inv.op == "==" and \
                        isinstance(ghost_inv.expr2, expr.AConst),\
                        'Please offer the the differential equation satisfied by the ghost variable.'

                    # Obtain dg/dx * dx
                    dg_x = compute_diff(ghost_inv.expr1, eqs_dict=self.infos[pos].eqs_dict)

                    # Obtain dg/dy
                    dgdy = compute_diff(ghost_inv.expr1, eqs_dict={ghost_var: expr.AConst(1)})

                    # Since dg/dx * dx + dg/dy * dy == 0, so dy = -(dg/dx * dx) / dg/dy
                    dy = expr.OpExpr("-", expr.OpExpr("/", dg_x, dgdy))
                    # Simplify dy
                    dy = self.simplify_expression(dy)

                    self.infos[pos].ghost_eqs = {ghost_var: dy}

                # Verify the reasonablity of ghost equations.
                # dy should be in the form: a(x) * y + b(x), y is not in a(x) or b(x)
                ghost_var_degree = degree(sympify(str(dy).replace('^', '**')), gen=symbols(ghost_var))
                if not ghost_var_degree in {0,1}:
                    raise AssertionError("Ghost equations should be linear in ghost variable!")

                # The denominator of dy cannot be equal to 0.
                denomi_not_zero = demoninator_not_zero(dy)
                vc2 = denomi_not_zero
                if not z3_prove(vc2):
                    raise AssertionError("The denominator in the ghost equations cannot be equal be zero!")
                        
                # Third condition
                vc3 = expr.imp(ghost_inv, dG_inv)

                self.infos[pos].vcs += [vc1, vc3]
                if dG_inv != post:
                    self.infos[pos].vcs.append(expr.imp(dG_inv, post))

                # New precondition is inv
                pre = dG_inv

            # Using dbx rule
            # Cases when dbx_inv is "e == 0".
                # Use Darboux Equality Rule
                #          D --> e_lie_deriv == g * e
                #--------------------------------------------    (g is the cofactor)
                #   {e == 0} <x_dot = f(x) & D> {e == 0}
            # Cases when dbx_inv is e >(>=) 0.
                # Use Darboux Inequality Rule.
                #           D --> e_lie_deriv >= g * e
                # ---------------------------------------------
                #    e >(>=) 0 <x_dot = f(x) & D> e >(>=) 0
            elif self.infos[pos].dbx_rule or \
                self.infos[pos].dbx_inv is not None or \
                self.infos[pos].dbx_cofactor is not None:

                # By default, dbx_inv is post.
                if self.infos[pos].dbx_inv is None:
                    self.infos[pos].dbx_inv = post
                else:
                    self.infos[pos].vcs.append(expr.imp(self.infos[pos].dbx_inv, post))
                dbx_inv = self.infos[pos].dbx_inv

                # For example, simplify ~(x > 1) to x <= 1
                dbx_inv = self.simplify_expression(dbx_inv)
                if not isinstance(dbx_inv, expr.RelExpr): 
                    print('dbx_inv:', dbx_inv, 'type:', type(dbx_inv))
                    raise NotImplementedError
                
                assert dbx_inv.op in {'==', '>', '>=', '<', '<='}

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
                # Compute the lie derivative of e.
                e_lie_deriv = compute_diff(e, eqs_dict=self.infos[pos].eqs_dict)

                # if self.wolfram_engine:
                    

                # Cases when dbx_inv is "e == 0".
                # Use Darboux Equality Rule
                #          D --> e_lie_deriv == g * e
                #--------------------------------------------    (g is the cofactor)
                #   {e == 0} <x_dot = f(x) & D> {e == 0}
                if dbx_inv.op == "==" :

                    # Cases when the cofactor g is not offered.
                    # Compute the cofactor g by auto.
                    if self.infos[pos].dbx_cofactor is None:
                        g = expr.OpExpr('/', e_lie_deriv, e)
                        g = self.simplify_expression(g)
                        self.infos[pos].dbx_cofactor = g

                        denomi_not_zero = expr.imp(expr.list_conj(*self.infos[pos].assume),
                                                   demoninator_not_zero(g))

                        # G_sym is supposed to be a reasonable expression.
                        if not z3_prove(denomi_not_zero):
                            raise AssertionError("The denominator of the cofactor cannot be equal to zero!")
                        else:
                            self.infos[pos].dbx_cofactor = g

                    # Cases when cofactor g is offered by the user.
                    else:
                        g = self.infos[pos].dbx_cofactor
                        
                        denomi_not_zero = expr.imp(expr.list_conj(*self.infos[pos].assume),
                                          demoninator_not_zero(g))

                        if not z3_prove(denomi_not_zero):
                            raise AssertionError("The denominator of the cofactor cannot be equal to zero!")

                        # Boundary of D --> e_lie_deriv == g * e
                        vc = expr.imp(constraint, expr.RelExpr('==', e_lie_deriv, 
                                                                    expr.OpExpr('*'), g, e))

                        self.infos[pos].vcs.append(vc)

                # Cases when dbx_inv is e >(>=) 0.
                # Use Darboux Inequality Rule.
                #           D --> e_lie_deriv >= g * e
                # ---------------------------------------------
                #    e >(>=) 0 <x_dot = f(x) & D> e >(>=) 0
                elif dbx_inv.op in {'>', '>='}:
                    # Cases when the cofactor g is not offered.
                    # Compute the cofactor automatically.
                    if self.infos[pos].dbx_cofactor is None:
                        quot_remains = self.polynomial_div(e_lie_deriv, e)
                        # print("quot:", quot, "remain:", remain)
                        # self.infos[pos].dbx_cofactor = quot

                        # Several quot and remain pairs may returned from the polynomial division.
                        # If there is a remain >= 0, there exists a quot satisfying g in dbx_rule.
                        vc_comps = []
                        for _, remain in quot_remains.items():
                            # remain (e_lie_deriv - g * e) >= 0.
                            vc_comp = expr.RelExpr('>=', remain, expr.AConst(0))
                            vc_comps.append(vc_comp)
                        vc = expr.list_disj(*vc_comps)

                        self.infos[pos].vcs.append(vc)

                    # Cases when the cofactor g is offered by the user.
                    else:
                        g = self.infos[pos].dbx_cofactor
                        denomi_not_zero = expr.imp(expr.list_conj(*self.infos[pos].assume),
                                        demoninator_not_zero(g))

                        if not z3_prove(denomi_not_zero):
                            raise AssertionError("The denominator of the cofactor cannot be equal to zero!")

                        vc = expr.imp(constraint, expr.RelExpr('>=', e_lie_deriv, 
                                                                    expr.OpExpr('*', self.infos[pos].dbx_cofactor, e)))
                        
                        self.infos[pos].vcs.append(vc)
                
                pre = dbx_inv   
          

            # Use barrier certificate
            #             D && e == 0 --> e_lie > 0
            # --------------------------------------------------
            #      {e >=(>) 0} <x_dot = f(x) & D> {e >=(>) 0}
            elif self.infos[pos].barrier_rule or\
                self.infos[pos].barrier_inv:

                # Use post as barrier invariant if it's not offered.
                if self.infos[pos].barrier_inv is None:
                    self.infos[pos].barrier_inv = post
                else:
                    self.infos[pos].vcs.append(expr.imp(self.infos[pos].barrier_inv, post))

                barrier_inv = self.infos[pos].barrier_inv

                pre = barrier_inv

                barrier_inv = self.simplify_expression(barrier_inv)
                # print("AAAA:", barrier_inv)

                assert barrier_inv.op in {'<=', '>=', '>', '<'}

                # TODO: e should be continous

                # Translate '<=' into '>='
                if barrier_inv.op == '<=':
                    barrier_inv = expr.RelExpr('>=', barrier_inv.expr2, barrier_inv.expr1)
                elif barrier_inv.op == '<':
                    barrier_inv = expr.RelExpr('>', barrier_inv.expr2, barrier_inv.expr1)

                # Translate 'e >= c' into 'e - c >= 0'
                if barrier_inv.expr2 != 0:
                    expr1 = expr.OpExpr('-', barrier_inv.expr1, barrier_inv.expr2)
                    expr1 = self.simplify_expression(expr1)
                    barrier_inv = expr.RelExpr(barrier_inv.op, expr1, expr.AConst(0))

                # print("BBBB:",barrier_inv)
                e = barrier_inv.expr1
                e_lie = compute_diff(e, eqs_dict=self.infos[pos].eqs_dict)


                vc = expr.imp(expr.LogicExpr('&&', constraint, 
                                                   expr.RelExpr('==', e, expr.AConst(0))),
                              expr.RelExpr('>', e_lie, expr.AConst(0)))

                self.infos[pos].vcs.append(vc)

            # Using Conjuntion Rule
                #  {P1} c {Q1}     {P2} c {Q2}   P --> P1 && P2
                #------------------------------------------------
                #               {P} c {Q1 && Q2}
            elif self.infos[pos].conj_rule:
                assert isinstance(post, expr.LogicExpr) and post.op == '&&'

                eqs_dict = self.infos[pos].eqs_dict
                sub_posts = expr.split_conj(post)

                # Compute wp for each sub_inv
                sub_pres = []
                for i, sub_post in enumerate(sub_posts):
                    # Create different CmdInfos for each sub-invariants
                    sub_pos = (pos[0], pos[1] + (i,))
                    if sub_pos not in self.infos:
                        self.infos[sub_pos] = CmdInfo()
                    self.infos[sub_pos].post = sub_post
                    self.infos[sub_pos].assume += self.infos[pos].assume
                    self.infos[sub_pos].eqs_dict = eqs_dict
                    self.compute_wp(pos=sub_pos)

                    sub_pres.append(self.infos[sub_pos].pre)

                pre = expr.list_conj(*sub_pres)             

            # # Using the rule below:(proved by Isabelle)
            # #    e > 0 --> e_lie_deriv >= 0
            # #----------------------------------    # c is an ODE
            # #           {e > 0} c {e > 0}
            # elif self.infos[pos].assume_inv:
            #     assume_inv = self.infos[pos].assume_inv
            #     assert assume_inv.op in ['>', '<']
                
            #     # Translate into '>' form.
            #     if assume_inv.op == '<':
            #         assume_inv = expr.RelExpr('>', assume_inv.expr2, assume_inv.expr1)

            #     # Translate into 'e > 0' form.
            #     if assume_inv.expr2 is not expr.AConst(0):
            #         assume_inv = expr.RelExpr('>', expr.OpExpr('-', assume_inv.expr1, assume_inv.expr2),\
            #             expr.AConst(0))

            #     # Compute the lie derivation of 'e > 0'
            #     differential = compute_diff(assume_inv, eqs_dict=self.infos[pos].eqs_dict)

            #     self.infos[pos].vcs.append(expr.imp(assume_inv, differential))
            #     pre = assume_inv

            else:
                raise AssertionError("No invariant set at position %s." % str(pos))

        elif isinstance(cur_hp, hcsp.Condition):
            # Condition, {P} cond -> c {Q}
            # the wp of Condition is cond --> wp of c
            cond = cur_hp.cond
            if not isinstance(cond, expr.BExpr):
                raise NotImplementedError

            sub_pos = (pos[0] + (0,), pos[1])
            if sub_pos not in self.infos:
                self.infos[sub_pos] = CmdInfo()
            self.infos[sub_pos].post = post
            self.compute_wp(pos=sub_pos)

            pre = expr.imp(cond, self.infos[sub_pos].pre)

        elif isinstance(cur_hp, hcsp.ITE):
            # ITE, if b then c1 else c2 endif
            #                       {P1} c1 {Q}  {P2} c2 {Q}  {P3} c3 {Q}
            #-----------------------------------------------------------------------------
            #              {(b1 --> P1) && (~b1 && b2 --> P2)&& (~b1 && ~b2 --> P3)} 
            #                      if b1 then c1 elif b2 then c2 else c3 endif 
            #                                         {Q}
            if_hps = cur_hp.if_hps

            sub_imp_list = []
            if_cond_list = []
            for i in range(len(if_hps) + 1):
                sub_pos = (pos[0] + (i,), pos[1])
                if sub_pos not in self.infos:
                    self.infos[sub_pos] = CmdInfo()
                self.infos[sub_pos].post = post
                self.infos[sub_pos].assume += self.infos[pos].assume

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
                    sub_cond =  expr.neg_expr(expr.list_disj(*if_cond_list[:]))

                # Compute the implicaiton for each if_hp or else_hp
                sub_imp = expr.imp(sub_cond, sub_pre)
                sub_imp_list.append(sub_imp)

            pre = expr.list_conj(*sub_imp_list)

        else:
            raise NotImplementedError

        # Assign pre-condition, or create a new verification condition if the
        # pre-condition is already set.
        if self.infos[pos].pre is None:
            self.infos[pos].pre = pre
        else:
            self.infos[pos].vcs.append(expr.imp(self.infos[pos].pre, pre))

        # Add assume into the hypothesis of every verification condition.
        if self.infos[pos].assume:
            assume = expr.list_conj(*self.infos[pos].assume)
            for i in range(len(self.infos[pos].vcs)):
                self.infos[pos].vcs[i] = expr.imp(assume, self.infos[pos].vcs[i])
        

    def get_all_vcs(self):
        all_vcs = dict()
        for pos, info in self.infos.items():
            if info.vcs:
                all_vcs[pos] = info.vcs
        return all_vcs

    def verify(self):
        """Verify all VCs in self."""
        all_vcs = self.get_all_vcs()
        if self.wolfram_engine:
            for pos, vcs in all_vcs.items():
                for vc in vcs:
                    if not wl_prove(vc):
                        print("The failed verification condition is :\n", pos, ':', str(vc))
                        return False
            return True

        elif self.z3:
            for pos, vcs in all_vcs.items():
                for vc in vcs:
                    if not z3_prove(vc):
                        print("The failed verification condition is :\n", pos, ':', str(vc))
                        return False
                    # else:
                        # print("The successful verificaiton condition is:", str(vc))
            return True
