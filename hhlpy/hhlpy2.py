"""
Python implementation of Hybrid Hoare Logic.

This version uses data structures that are separate from the main
HCSP program.

"""

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp.simulator import get_pos
from hhlpy.z3wrapper import z3_prove
from sympy import sympify, degree, symbols, factor_list, fraction, simplify
from ss2hcsp.hcsp.parser import aexpr_parser


def compute_diff(e, eqs_dict):
    """Compute differential of an arithmetic or boolean expression."""
    def rec(e):
        if isinstance(e, expr.LogicExpr):
            if e.op == "&&":
                return expr.LogicExpr("&&", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == "||":
                 return expr.LogicExpr("&&", rec(e.exprs[0]), rec(e.exprs[1]))
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
                return expr.OpExpr("+", expr.OpExpr("*", e.exprs[0], dv), expr.OpExpr("*", du, e.exprs[1]))
            elif e.op == '^' and isinstance(e.exprs[1], expr.AConst):
                # d(u^n) = n * u^(n-1) * du
                du = rec(e.exprs[0])
                mid_expr = expr.OpExpr("^", e.exprs[0], expr.OpExpr("-", e.exprs[1], expr.AConst(1)))
                return expr.OpExpr("*", e.exprs[1], expr.OpExpr("*", mid_expr, du)) 
            elif e.op == '/':
                # d(u/v) = (u*dv + du * v)/ v^2
                # If v is constant, d(u/v) = 1/v * du, which is easier than using above rule.
                if isinstance(e.exprs[1], expr.AConst) or \
                   isinstance(e.expr[1], expr.FunExpr) and len(e.exprs == 0): # actually a constant
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
    if not isinstance(e, str):
        e = str(e)
    
    e = simplify(sympify(e))
    _, denominator = fraction(e)
    denominator = aexpr_parser.parse(str(denominator))

    return expr.RelExpr('!=', denominator, expr.AConst(0))

class CmdInfo:
    """Information associated to each HCSP program."""
    def __init__(self):
        # Pre-condition and post-condition are assertions.
        self.pre = None
        self.post = None

        # List of verification conditions for this command.
        self.vcs = []

        # Invariants for loops.
        self.loop_inv = None

        # Equation dict for ODEs.
        self.eqs_dict = dict()

        # Assumptions for HCSPs.
        self.assume = []

        # Use differential weakening rule or not
        self.dw = False

        # Invariants for ODEs.
        self.ode_inv = None

        # Differential invariants for ODEs.
        self.diff_inv = None

        # Assume invariants for ODEs.
        self.assume_inv = None

        # Differential cuts for ODES.
        self.diff_cuts = []

        # Ghost invariants for ODEs.
        self.ghost_inv = None

        # Computed differential equations for ghosts.
        self.ghost_eqs = dict()

        # Use dbx rule or not
        self.dbx_rule = False

        # Dbx cofactor for ODEs
        self.dbx_cofactor = None 

    def __str__(self):
        res = ""
        res += "pre = %s\n" % self.pre
        res += "post = %s\n" % self.post
        for vc in self.vcs:
            res += "vc: %s\n" % vc
        if self.inv is not None:
            res += "inv: %s\n" % self.inv
        if self.diff_inv is not None:
            res += "diff_inv: %s\n" % self.diff_inv
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
    def __init__(self, *, pre, hp, post, constants=set()):
        # The HCSP program to be verified.
        self.hp = hp

        # Mapping from program position to CmdInfo objects.
        self.infos = dict()

        # Set of names that are used
        self.names = hp.get_vars().union(pre.get_vars()).union(post.get_vars())

        # Set of constants that are used
        self.constants = constants

        # Set of variable names that are used
        self.vars = self.names - self.constants

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
        if not self.constants.isdisjoint(pre.get_vars()):
            # Assume pre is a Conjunction Expression.
            pre_list = expr.split_conj(pre)
            for sub_pre in pre_list:
                # The sub_pre cannot include variables.
                if sub_pre.get_vars().isdisjoint(self.vars):
                    self.infos[root_pos].assume.append(sub_pre)

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

    def add_loop_invariant(self, pos, loop_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].loop_inv = loop_inv

    def add_ode_invariant(self, pos, ode_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].ode_inv = ode_inv

    def set_diff_weakening(self, pos, dw):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].dw = dw

    def add_diff_invariant(self, pos, diff_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].diff_inv = diff_inv

    def add_assume_invariant(self, pos, assume_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].assume_inv = assume_inv

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

    def use_darboux_rule(self, pos, dbx_rule):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].dbx_rule = dbx_rule

    def add_darboux_cofactor(self, pos, dbx_cofactor):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].dbx_cofactor = dbx_cofactor

    def compute_wp(self, *, pos=((),())):
        """Compute weakest-preconditions using the given information."""

        # Obtain the hp at the given position
        cur_hp = get_pos(self.hp, pos[0])

        # The post-condition at the given position should already be
        # available.
        assert pos in self.infos and self.infos[pos].post is not None
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
            #               pre: cur_hp.expr(newvar_name|var_name) --> post(newvar_name|var_name)
            if not isinstance(cur_hp.var_name, expr.AVar):
                raise NotImplementedError
            if cur_hp.var_name in self.constants:
                raise NotImplementedError("Constants can not be assigned")

            var_str = cur_hp.var_name.name

            # Create a new var
            i = 0
            newvar_str = var_str + str(i)
            while(newvar_str in self.names):
                i = i + 1
                newvar_str = var_str + str(i)
            self.names.add(newvar_str)

            #Compute the pre: hp.expr(newvar_name|var_name) --> post(newvar_name|var_name)
            newvar_name = expr.AVar(newvar_str)
            pre = expr.imp(cur_hp.expr.subst({var_str: newvar_name}), post.subst({var_str: newvar_name}))


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

            # Verification condition is invariant --> pre_loopbody and invariant --> post
            vc1 = expr.imp(inv, pre_loopbody)
            vc2 = expr.imp(inv, post)
            self.infos[pos].vcs = [vc1, vc2]

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

            # By default, ode_inv is post.
            if not self.infos[pos].ode_inv:
                self.infos[pos].ode_inv = self.infos[pos].post
            
            # Use dW rule
            # Note: remain unproved!
            # When dw is True.
            #      Boundary of D --> Q || Q --> ~D
            #------------------------------------------
            #         {Q} <x_dot = f(x) & D> {Q}
            if self.infos[pos].dw:

                boundary = compute_boundary(constraint)
                self.infos[pos].vcs.append(expr.LogicExpr('||', expr.imp(boundary, post), \
                                                            expr.imp(post, expr.neg_expr(constraint))))  

                pre = post 

            # Use dI rules
            # When diff_inv is set or by default
            elif self.infos[pos].diff_inv is not None or \
                not self.infos[pos].dw and self.infos[pos].diff_inv is None and \
                not self.infos[pos].diff_cuts and self.infos[pos].ghost_inv is None and \
                not self.infos[pos].dbx_rule and not self.infos[pos].dbx_cofactor and \
                self.infos[pos].assume_inv is None and \
                (self.infos[pos].ode_inv is None or isinstance(self.infos[pos].ode_inv, expr.RelExpr)):
               
                if self.infos[pos].diff_inv is not None:
                    diff_inv = self.infos[pos].diff_inv
                # By default, using post as diff_inv
                else:
                    diff_inv = post

                # ode_inv can be written in when using Conjuntion Rule.
                # if self.infos[pos].ode_inv is not None:
                #     assert diff_inv == self.infos[pos].ode_inv
                if not isinstance(diff_inv, expr.BExpr):
                    raise AssertionError('Invalid differential invariant for ODE!')               

                # Compute the differential of inv.
                # Compute the boundary of constraint. 
                # One semi-verification condition is boundary of constraint --> differential of inv.
                differential = compute_diff(diff_inv, eqs_dict=self.infos[pos].eqs_dict)
                boundary = compute_boundary(constraint)
                vc1 = expr.imp(boundary, differential)
                
                
                # The second condition is inv --> post.
                vc2 = expr.imp(diff_inv, post)

                self.infos[pos].vcs = [vc1, vc2]

                pre = diff_inv
            
            # Use dC rules
            #  {P1} c {R1}    R1--> {P2} c {R2}     R1 && R2--> {P3} c {I}
            #-----------------------------------------------------------
            #                        {P1 && P2 && P3} c {I}
            elif self.infos[pos].diff_cuts:
                diff_cuts = self.infos[pos].diff_cuts
                
                # Record the pre of each subproof
                pre_list =[]

                # Compute wp for each subproof, whose assume is the conjunction of diff_cuts.
                for i in range(len(diff_cuts) + 1):
                    if i < len(diff_cuts) and not isinstance(diff_cuts[i], expr.BExpr):
                        raise NotImplementedError("Invalid differential cut for ODE!")

                    # Create CmdInfo for every subproof.
                    sub_pos = (pos[0], pos[1] + (i,))
                    if sub_pos not in self.infos:
                        self.infos[sub_pos] = CmdInfo()

                    # Post of the last subproof is the post of the whole proof.
                    # Others' posts are diff_cuts[i].
                    if i < len(diff_cuts):
                        self.infos[sub_pos].post = diff_cuts[i]
                    else:
                        self.infos[sub_pos].post = post

                    # If i == 0, no update for assume, else, assume is updated by adding diff_cuts[:i].
                    if i != 0:
                        self.infos[sub_pos].assume = self.infos[sub_pos].assume + diff_cuts[:i]

                    self.compute_wp(pos=sub_pos)

                    pre_list.append(self.infos[sub_pos].pre)

                pre = expr.list_conj(*pre_list)

            # Use dG rules
            elif self.infos[pos].ghost_inv is not None:
                ghost_inv = self.infos[pos].ghost_inv
                ode_inv = self.infos[pos].ode_inv

                if ode_inv is None or not isinstance(ode_inv, expr.BExpr):
                    raise NotImplementedError('Invalid invariant for ODE (ghost mode)!')
                if not isinstance(ghost_inv, expr.BExpr):
                    raise NotImplementedError('Invalid ghost invariant for ODE!')

                ghost_vars = [v for v in ghost_inv.get_vars() if v not in self.names]
                if len(ghost_vars) != 1:
                    raise AssertionError("Number of ghost variables is not 1.")
                ghost_var = ghost_vars[0]
                self.names.add(ghost_var)

                if not self.infos[pos].eqs_dict:
                    for name, deriv in cur_hp.eqs:
                        self.infos[pos].eqs_dict[name] = deriv

                # The first condition is: inv implies there exists a value of ghost_var
                # that satisfies ghost_inv.
                vc1 = expr.imp(ode_inv, expr.ExistsExpr(ghost_var, ghost_inv))

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
                    dy = simplify(sympify(str(ghost_eqs[ghost_var])))

                    # Create a new CmdInfo for the ODE with ghost_eqs
                    sub_pos = (pos[0], pos[1] + (0,))

                    if sub_pos not in self.infos:
                        self.infos[sub_pos] = CmdInfo()

                    self.infos[sub_pos].post = ghost_inv
                    self.infos[sub_pos].ode_inv = ghost_inv

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
                    dy = simplify(sympify(str(dy)))

                    self.infos[pos].ghost_eqs = {ghost_var: aexpr_parser.parse(str(dy))}

                # Verify the reasonablity of ghost equations.
                # dy should be in the form: a(x) * y + b(x), y is not in a(x) or b(x)
                ghost_var_degree = degree(dy, gen=symbols(ghost_var))
                if not ghost_var_degree in {0,1}:
                    raise AssertionError("Ghost equations should be linear in ghost variable!")

                # The denominator of dy cannot be equal to 0.
                denomi_not_zero = demoninator_not_zero(dy)
                vc2 = denomi_not_zero
                        
                # Third condition
                vc3 = expr.imp(ghost_inv, ode_inv)

                # Fourth condition
                vc4 = expr.imp(ode_inv, post)

                self.infos[pos].vcs = [vc1, vc2, vc3, vc4]

                # New precondition is inv
                pre = ode_inv

            # Using dbx rule
            elif self.infos[pos].dbx_rule or self.infos[pos].dbx_cofactor is not None:
                ode_inv = self.infos[pos].ode_inv

                if not isinstance(ode_inv, expr.RelExpr): 
                    raise NotImplementedError
                
                assert ode_inv.op in {'==', '>', '>=', '<', '<='}

                # Tranlate '<' and '<=' into '>' and '>='.
                if ode_inv.op == '<':
                    ode_inv = expr.RelExpr('>', ode_inv.expr2, ode_inv.expr1)
                elif ode_inv.op == '<=':
                    ode_inv = expr.RelExpr('>=', ode_inv.expr2, ode_inv.expr1)

                # Translate into the form e == 0 or e >(>=) 0
                if ode_inv.expr2 != expr.AConst(0):
                    ode_inv = expr.RelExpr(ode_inv.op, expr.OpExpr('-', ode_inv.expr1, ode_inv.expr2), 
                                                                        expr.AConst(0)) 
                
                # Compute the lie derivative of e.
                lie_deriv = compute_diff(ode_inv.expr1, eqs_dict=self.infos[pos].eqs_dict)

                # Cases when ode_inv is "e == 0".
                # Use Darboux Equality Rule
                #          D --> e_lie_deriv == g * e
                #--------------------------------------------    (g is the cofactor)
                #   {e == 0} <x_dot = f(x) & D> {e == 0}
                if ode_inv.op == "==" :

                    # # Compute the boundary of constraint.
                    # boundary = compute_boundary(constraint)

                    # Compute the cofactor g by auto if it's not offered.
                    if self.infos[pos].dbx_cofactor is None:
                        g = expr.OpExpr('/', lie_deriv, ode_inv.expr1)
                        g_sym = simplify(sympify(str(g)))
                        self.infos[pos].dbx_cofactor = aexpr_parser.parse(str(g_sym))

                        denomi_not_zero = demoninator_not_zero(g_sym)

                        # G_sym is supposed to be a reasonable expression.
                        self.infos[pos].vcs.append(expr.imp(constraint, denomi_not_zero))

                    # Cases when cofactor g is offered by the user.
                    else:
                        g = self.infos[pos].dbx_cofactor
                        
                        denomi_not_zero = demoninator_not_zero(g)

                        vc1 = expr.imp(constraint, denomi_not_zero)
                        # Boundary of D --> e_lie_deriv == g * e
                        vc2 = expr.imp(constraint, expr.RelExpr('==', lie_deriv, 
                                                                    expr.OpExpr('*'), g, ode_inv.expr1))

                        self.infos[pos].dbx_cofactor = [vc1, vc2]

                    pre = ode_inv

                # Cases when ode_inv is e >(>=) 0.
                # Use Darboux Inequality Rule.
                #           D --> e_lie_deriv >= g * e
                # ---------------------------------------------
                #    e >(>=) 0 <x_dot = f(x) & D> e >(>=) 0
                if ode_inv.op in {'>', '>='}:
                    if self.infos[pos].dbx_cofactor is None:
                        raise NotImplementedError("Please offer the cofactor for dbx inequality rule!")

                    g = self.infos[pos].dbx_cofactor
                    denomi_not_zero = demoninator_not_zero(g)

                    vc1 = expr.imp(constraint, denomi_not_zero)

                    vc2 = expr.imp(constraint, expr.RelExpr('>=', lie_deriv, 
                                                                  expr.OpExpr('*', g, ode_inv.expr1)))

                    self.infos[pos].vcs = [vc1, vc2]


                    pre = ode_inv              

            # Using Conjuntion Rule
            #  {I1} c {I1}     {I2} c {I2}
            #-------------------------------
            #    {I1 && I2} c {I1 && I2}
            # Invariant is a conjunction expression, such as x > 0 && y > 0, we can compute wp for each sub_inv one by one.
            # Different sub_inv may use different ODE rules
            elif self.infos[pos].ode_inv is not None and isinstance(self.infos[pos].ode_inv, expr.LogicExpr):
                ode_inv = self.infos[pos].ode_inv
                eqs_dict = self.infos[pos].eqs_dict

                assert ode_inv.op == "&&"
                sub_invs = expr.split_conj(ode_inv)
                
                # Compute wp for each sub_inv
                for i, sub_inv in enumerate(sub_invs):
                    # Create different CmdInfos for each sub-invariants
                    sub_pos = (pos[0], pos[1] + (i,))
                    if sub_pos not in self.infos:
                        self.infos[sub_pos] = CmdInfo()
                    self.infos[sub_pos].post = sub_inv
                    self.infos[sub_pos].eqs_dict = eqs_dict
                    self.infos[sub_pos].ode_inv = sub_inv
                    
                    self.compute_wp(pos=sub_pos)
                pre = ode_inv

            # Using the rule below:(proved by Isabelle)
            #    e > 0 --> e_lie_deriv >= 0
            #--------------------------    # c is an ODE, e_lie_deriv represent the lie derivation of e
            #    {e > 0} c {e > 0}
            elif self.infos[pos].assume_inv:
                assume_inv = self.infos[pos].assume_inv
                assert assume_inv.op in ['>', '<']
                
                # Translate into '>' form.
                if assume_inv.op == '<':
                    assume_inv = expr.RelExpr('>', assume_inv.expr2, assume_inv.expr1)

                # Translate into 'e > 0' form.
                if assume_inv.expr2 is not expr.AConst(0):
                    assume_inv = expr.RelExpr('>', expr.OpExpr('-', assume_inv.expr1, assume_inv.expr2),\
                        expr.AConst(0))

                # Compute the lie derivation of 'e > 0'
                differential = compute_diff(assume_inv, eqs_dict=self.infos[pos].eqs_dict)

                self.infos[pos].vcs.append(expr.imp(assume_inv, differential))
                pre = assume_inv

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
        for _, vcs in all_vcs.items():
            if not all(z3_prove(vc) for vc in vcs):
                return False
        return True
