"""Expressions"""


class AExpr:  # Arithmetic expression
    def __init__(self):
        pass

    def get_vars(self):
        """Returns set of variables in the expression."""
        raise NotImplementedError

    def subst(self, inst):
        """inst is a dictionary mapping variable names to expressions."""
        raise NotImplementedError


class AVar(AExpr):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return "Var(%s)" % self.name

    def __str__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, AVar) and self.name == other.name

    def __hash__(self):
        return hash(("AVar", self.name))

    def get_vars(self):
        return {self.name}

    def subst(self, inst):
        if self.name in inst:
            return inst[self.name]
        else:
            return self


class AConst(AExpr):
    def __init__(self, value):
        assert isinstance(value, (int, float))
        self.value = value

    def __repr__(self):
        return "Const(%s)" % str(self.value)

    def __str__(self):
        return str(self.value)

    def __eq__(self, other):
        return isinstance(other, AConst) and self.value == other.value

    def __hash__(self):
        return hash(("AConst", self.value))

    def get_vars(self):
        return set()

    def subst(self, inst):
        return self


class PlusExpr(AExpr):
    def __init__(self, signs, exprs):
        self.signs = signs
        self.exprs = exprs

    def __repr__(self):
        val = ", ".join(sign + repr(expr) for sign, expr in zip(self.signs, self.exprs))
        return "Plus(%s)" % val

    def __str__(self):
        if self.signs[0] == '+':
            res = str(self.exprs[0])
        else:
            res = '-' + str(self.exprs[0])
        for sign, expr in zip(self.signs[1:], self.exprs[1:]):
            res += sign + str(expr)
        return res

    def __eq__(self, other):
        return isinstance(other, PlusExpr) and self.signs == other.signs and self.exprs == other.exprs

    def __hash__(self):
        return hash(("Plus", tuple(self.signs), tuple(self.exprs)))

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return PlusExpr(self.signs, [expr.subst(inst) for expr in self.exprs])


class TimesExpr(AExpr):
    def __init__(self, signs, exprs):
        self.signs = signs
        self.exprs = exprs

    def __repr__(self):
        val = ", ".join(sign + repr(expr) for sign, expr in zip(self.signs, self.exprs))
        return "Times(%s)" % val

    def __str__(self):
        if self.signs[0] == '*':
            res = str(self.exprs[0])
        else:
            res = '1/' + str(self.exprs[0])
        for sign, expr in zip(self.signs[1:], self.exprs[1:]):
            res += sign + str(expr)
        return res

    def __eq__(self, other):
        return isinstance(other, TimesExpr) and self.signs == other.signs and self.exprs == other.exprs

    def __hash__(self):
        return hash(("Times", tuple(self.signs), tuple(self.exprs)))

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return TimesExpr(self.signs, [expr.subst(inst) for expr in self.exprs])


class FunExpr(AExpr):
    def __init__(self, fun_name, exprs):
        assert fun_name in ["min", "max", "abs", "gcd"]
        self.fun_name = fun_name
        self.exprs = exprs

    def __repr__(self):
        return "Fun(%s, %s)" % (self.fun_name, ", ".join(repr(expr) for expr in self.exprs))

    def __str__(self):
        return "%s(%s)" % (self.fun_name, ", ".join(str(expr) for expr in self.exprs))

    def __eq__(self, other):
        return isinstance(other, FunExpr) and self.fun_name == other.fun_name and \
            self.exprs == other.exprs

    def __hash__(self):
        return hash(("Fun", self.fun_name, tuple(self.exprs)))

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return FunExpr(self.fun_name, [expr.subst(inst) for expr in self.exprs])


class ModExpr(AExpr):
    def __init__(self, expr1, expr2):
        assert isinstance(expr1, AVar) and isinstance(expr2, AExpr)
        self.expr1 = expr1
        self.expr2 = expr2

    def __repr__(self):
        return "Mod(%s, %s)" % (str(self.expr1), str(self.expr2))

    def __str__(self):
        return "%s%%%s" % (str(self.expr1), str(self.expr2))

    def __eq__(self, other):
        return isinstance(other, ModExpr) and self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("Mod", self.expr1, self.expr2))

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def subst(self, inst):
        return ModExpr(expr1=self.expr1.subst(inst), expr2=self.expr2.subst(inst))


class BExpr:
    def __init__(self):
        pass

    def get_vars(self):
        raise NotImplementedError

    def subst(self, inst):
        raise NotImplementedError


class BConst(BExpr):  # Boolean expression
    def __init__(self, value):
        assert isinstance(value, bool)
        self.value = value

    def __repr__(self):
        return "BConst(%s)" % str(self.value)

    def __str__(self):
        return str(self.value)

    def __eq__(self, other):
        return isinstance(other, BConst) and self.value == other.value

    def __hash__(self):
        return hash(("BConst", self.value))

    def get_vars(self):
        return set()

    def subst(self, inst):
        return self


true_expr = BConst(True)
false_expr = BConst(False)


class LogicExpr(BExpr):
    def __init__(self, op, expr1, expr2):
        assert op in ["&&", "||", "-->", "<-->"]
        assert isinstance(expr1, BExpr) and isinstance(expr2, BExpr)
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2

    def __repr__(self):
        return "Logic(%s, %s, %s)" % (self.op, repr(self.expr1), repr(self.expr2))

    def __str__(self):
        return str(self.expr1) + " " + self.op + " " + str(self.expr2)

    def __eq__(self, other):
        return isinstance(other, LogicExpr) and self.op == other.op and \
            self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("Logic", self.op, self.expr1, self.expr2))

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def subst(self, inst):
        return LogicExpr(self.op, self.expr1.subst(inst), self.expr2.subst(inst))


def conj(*args):
    assert isinstance(args, tuple) and all(isinstance(arg, BExpr) for arg in args)
    if len(args) == 0:
        return true_expr
    elif len(args) == 1:
        return args[0]
    else:
        return LogicExpr("&&", args[0], conj(*args[1:]))


def disj(*args):
    assert isinstance(args, tuple) and all(isinstance(arg, BExpr) for arg in args)
    if len(args) == 0:
        return false_expr
    elif len(args) == 1:
        return args[0]
    else:
        return LogicExpr("||", args[0], disj(*args[1:]))


def imp(b1, b2):
    return LogicExpr("-->", b1, b2)


class RelExpr(BExpr):
    neg_table = {"<": ">=", ">": "<=", "==": "!=", "!=": "==", ">=": "<", "<=": ">"}

    def __init__(self, op, expr1, expr2):
        assert op in ["<", ">", "==", "!=", ">=", "<="]
        assert isinstance(expr1, AExpr) and isinstance(expr2, AExpr)
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2

    def __repr__(self):
        return "Rel(%s, %s, %s)" % (self.op, repr(self.expr1), repr(self.expr2))

    def __str__(self):
        return str(self.expr1) + " " + self.op + " " + str(self.expr2)

    def __eq__(self, other):
        return isinstance(other, RelExpr) and self.op == other.op and \
            self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("Rel", self.op, self.expr1, self.expr2))

    def neg(self):
        return RelExpr(RelExpr.neg_table[self.op], self.expr1, self.expr2)

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def subst(self, inst):
        return RelExpr(self.op, self.expr1.subst(inst), self.expr2.subst(inst))


class Conditional_Inst:
    """A mapping from variables to lists of conditional substitutions.

    For example:
    {
        x: [(True, y + 1)],
        z: [(x >= 1, y + 1), (x < 1, y - 1)]
    }
    """
    def __init__(self):
        self.data = dict()

    def __repr__(self):
        def repr_pair(cond, inst):
            return "(%s, %s)" % (str(cond), str(inst))

        def repr_cond_inst(cond_inst):
            return "[" + ", ".join(repr_pair(cond, inst) for cond, inst in cond_inst) + "]"

        return "\n".join(var + ": " + repr_cond_inst(cond_inst) for var, cond_inst in self.data.items())

    def add(self, var_name, cond_inst):
        """Add a new instantiation."""
        assert var_name not in self.data
        
        # Substitute using existing instantiations
        for var in self.data:
            new_cond_inst = []
            for cond, expr in cond_inst:
                if var in cond.get_vars() or var in expr.get_vars():
                    for cond2, expr2 in self.data[var]:
                        if cond == true_expr:
                            new_cond = cond2
                        elif cond2 == true_expr:
                            new_cond = cond.subst({var: expr2})
                        else:
                            new_cond = conj(cond.subst({var: expr2}), cond2)
                        new_expr = expr.subst({var: expr2})
                        new_cond_inst.append((new_cond, new_expr))
                else:
                    new_cond_inst.append((cond, expr))
            cond_inst = new_cond_inst

        # Merge (cond, expr) pairs with the same expression
        expr_dict = dict()
        for cond, expr in cond_inst:
            if expr not in expr_dict:
                expr_dict[expr] = []
            expr_dict[expr].append(cond)

        cond_inst = []
        for expr, conds in expr_dict.items():
            cond_inst.append((disj(*conds), expr))

        self.data[var_name] = cond_inst
