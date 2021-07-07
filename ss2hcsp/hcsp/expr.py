"""Expressions"""

import math
import itertools
from ss2hcsp.matlab import function


def opt_round(x):
    if abs(round(x, 3) - x) < 1e-7:
        return round(x, 3)
    else:
        return x

def get_range(start, end):
    """Returns a range of numbers between start and end, inserting
    multiples of 0.1 along the way.

    """
    start_int = math.ceil(start * 10)
    end_int = math.floor(end * 10)
    res = []
    if start * 10 != start_int:
        res.append(start)
    for i in range(start_int, end_int+1):
        res.append(i / 10)
    if end * 10 != end_int:
        res.append(end)
    return res

def str_of_val(val):
    """Print form of a string."""
    if val is None:
        return ""
    elif isinstance(val, float):
        return str(round(val, 3))
    elif isinstance(val, dict):
        return "{" + (','.join(k + ':' + str(v) for k, v in val.items())) + "}"
    elif isinstance(val, str):
        return "\"" + val + "\""
    elif isinstance(val, list):
        return "[" + ",".join(str_of_val(v) for v in val) + "]"
    else:
        return str(val)


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
        super(AVar, self).__init__()
        assert isinstance(name, str)
        self.name = name

    def __repr__(self):
        return "AVar(%s)" % self.name

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
        super(AConst, self).__init__()
        assert isinstance(value, (int, float, list, str,function.AConst,function.ListExpr,function.ListExpr2,function.Var))
        if isinstance(value, list):
            self.value = list(value)
        else:
            self.value = value

    def __repr__(self):
        return "AConst(%s)" % str_of_val(self.value)

    def __str__(self):
        return str_of_val(self.value)

    def __eq__(self, other):
        return isinstance(other, AConst) and self.value == other.value

    def __hash__(self):
        return hash(("AConst", str(self.value)))

    def get_vars(self):
        return set()

    def subst(self, inst):
        return self


class PlusExpr(AExpr):
    def __init__(self, signs, exprs):
        super(PlusExpr, self).__init__()
        assert all(sign in ('+', '-') for sign in signs)
        assert all(isinstance(expr, AExpr) for expr in exprs)
        self.signs = signs
        self.exprs = exprs

    def __repr__(self):
        val = ", ".join(sign + repr(expr) for sign, expr in zip(self.signs, self.exprs))
        return "Plus(%s)" % val

    def __str__(self):
        res = str(self.exprs[0])
        if self.signs[0] == "-":
            if str(self.exprs[0]).startswith("-") or isinstance(self.exprs[0], PlusExpr):
                res = "-(" + res + ")"
            else:
                res = "-" + res
        for sign, expr in zip(self.signs[1:], self.exprs[1:]):
            if str(expr).startswith("-") or (sign == "-" and isinstance(expr, PlusExpr)):
                res += sign + "(" + str(expr) + ")"
            else:
                res += sign + str(expr)
        return res

    def __eq__(self, other):
        return isinstance(other, PlusExpr) and "".join(self.signs) == "".join(other.signs) and \
               list(self.exprs) == list(other.exprs)

    def __hash__(self):
        return hash(("Plus", tuple(self.signs), tuple(self.exprs)))

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return PlusExpr(self.signs, [expr.subst(inst) for expr in self.exprs])


class TimesExpr(AExpr):
    def __init__(self, signs, exprs):
        super(TimesExpr, self).__init__()
        self.signs = signs
        self.exprs = exprs

    def __repr__(self):
        val = ", ".join(sign + repr(expr) for sign, expr in zip(self.signs, self.exprs))
        return "Times(%s)" % val

    def __str__(self):
        res = str(self.exprs[0])
        if isinstance(self.exprs[0], PlusExpr) or (self.signs[0] == "/" and isinstance(self.exprs[0], TimesExpr)):
            res = "(" + res + ")"
        if self.signs[0] == "/":
            res = "1/" + res
        for sign, expr in zip(self.signs[1:], self.exprs[1:]):
            if isinstance(expr, PlusExpr) or (sign == "/" and isinstance(expr, TimesExpr)) \
                    or (sign == "*" and str(expr).startswith("-")):
                res += sign + "(" + str(expr) + ")"
            else:
                res += sign + str(expr)
        return res

    def __eq__(self, other):
        return isinstance(other, TimesExpr) and "".join(self.signs) == "".join(other.signs) and \
               list(self.exprs) == list(other.exprs)

    def __hash__(self):
        return hash(("Times", tuple(self.signs), tuple(self.exprs)))

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return TimesExpr(self.signs, [expr.subst(inst) for expr in self.exprs])


class FunExpr(AExpr):
    def __init__(self, fun_name, exprs):
        super(FunExpr, self).__init__()
        # assert fun_name in [
        #     "min", "max", "abs", "gcd", "delay", "sqrt", "div",
        #     "push", "pop", "top", "get", "bottom", "len", "get_max", "pop_max","get_min", "pop_min",
        #     "bernoulli", "uniform"]
        self.fun_name = fun_name
        exprs = tuple(exprs)
        assert all(isinstance(expr, AExpr) for expr in exprs)
        self.exprs = exprs

    def __repr__(self):
        return "Fun(%s, %s)" % (self.fun_name, ", ".join(repr(expr) for expr in self.exprs))

    def __str__(self):
        return "%s(%s)" % (self.fun_name, ",".join(str(expr) for expr in self.exprs))

    def __eq__(self, other):
        return isinstance(other, FunExpr) and self.fun_name == other.fun_name and \
               self.exprs == other.exprs

    def __hash__(self):
        return hash(("Fun", self.fun_name, self.exprs))

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return FunExpr(self.fun_name, [expr.subst(inst) for expr in self.exprs])


class ModExpr(AExpr):
    def __init__(self, expr1, expr2):
        super(ModExpr, self).__init__()
        assert isinstance(expr1, AExpr) and isinstance(expr2, AExpr)
        self.expr1 = expr1
        self.expr2 = expr2

    def __repr__(self):
        return "Mod(%s, %s)" % (repr(self.expr1), str(repr(self.expr2)))

    def __str__(self):
        s1, s2 = str(self.expr1), str(self.expr2)
        if isinstance(self.expr1, PlusExpr):
            s1 = '(' + s1 + ')'
        if isinstance(self.expr2, PlusExpr):
            s2 = '(' + s2 + ')'
        return "%s%%%s" % (s1, s2)

    def __eq__(self, other):
        return isinstance(other, ModExpr) and self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("Mod", self.expr1, self.expr2))

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def subst(self, inst):
        return ModExpr(expr1=self.expr1.subst(inst), expr2=self.expr2.subst(inst))


class ListExpr(AExpr):
    """List expressions."""
    def __init__(self, *args):
        super(ListExpr, self).__init__()
        args = tuple(args)
        assert all(isinstance(arg, AExpr) for arg in args)
        self.args = args
        self.count = 0

    def __repr__(self):
        return "List(%s)" % (','.join(repr(arg) for arg in self.args))

    def __str__(self):
        return "[%s]" % (','.join(str(arg) for arg in self.args))

    def __eq__(self, other):
        return isinstance(other, ListExpr) and self.args == other.args

    def __hash__(self):
        return hash(("List", self.args))
    
    def __iter__(self):
        return self

    def __len__(self):
      
       return len(self.args)
    def __getitem__(self,key):
            return self.args[key]

    def __next__(self):
        if self.count < len(self.args):
            result = self.args[self.count]
            self.count += 1
            return result
        else:
            raise StopIteration
  

    def get_vars(self):
        return set().union(*(arg.get_vars() for arg in self.args))

    def subst(self, inst):
        return ListExpr(*(expr.subst(inst) for expr in self.args))


class DictExpr(AExpr):
    """Dictionary expressions (structures)."""
    def __init__(self, *args):
        """Argument is a list of key-value pairs. Each key should be a string."""
        super(DictExpr, self).__init__()
        self.dict = dict()
        args = tuple(args)
        assert all(isinstance(k, str) and isinstance(v, AExpr) for k, v in args)
        for k, v in args:
            self.dict[k] = v

    def __repr__(self):
        return "Dict(%s)" % (','.join(k + ':' + repr(v) for k, v in self.dict.items()))

    def __str__(self):
        return "{%s}" % (','.join(k + ':' + str(v) for k, v in self.dict.items()))

    def __eq__(self, other):
        return isinstance(other, DictExpr) and self.dict == other.dict

    def __hash__(self):
        return hash(("Dict", tuple((k, v) for k, v in self.dict.items())))

    def get_vars(self):
        return set().union(*(v.get_vars() for k, v in self.dict.items()))

    def subst(self, inst):
        return DictExpr(*((k, v.subst(inst)) for k, v in self.dict.items()))


class ArrayIdxExpr(AExpr):
    """Expressions of the form a[i], where a evaluates to a list and i
    evaluates to an integer. Constructor also supports the case where the
    second argument is a list.
    
    """
    def __init__(self, expr1, expr2):
        super(ArrayIdxExpr, self).__init__()
        if isinstance(expr1, str):
            expr1 = AVar(expr1)
        assert isinstance(expr1, AExpr)
        if isinstance(expr2, AExpr):
            self.expr1 = expr1
            self.expr2 = expr2
        else:
            assert isinstance(expr2, (list, tuple)) and len(expr2) >= 1
            if len(expr2) == 1:
                self.expr1 = expr1
                self.expr2 = expr2[0]
            else:
                self.expr1 = ArrayIdxExpr(expr1, expr2[:-1])
                self.expr2 = expr2[-1]

    def __repr__(self):
        return "ArrayIdxExpr(%s,%s)" % (repr(self.expr1), repr(self.expr2))

    def __str__(self):
        return "%s[%s]" % (str(self.expr1), str(self.expr2))

    def __eq__(self, other):
        return isinstance(other, ArrayIdxExpr) and self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("ArrayIdx", self.expr1, self.expr2))

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def subst(self, inst):
        return ArrayIdxExpr(expr1=self.expr1.subst(inst), expr2=self.expr2.subst(inst))

class ArrayIdxExpr1(AExpr):
    """Expressions of the form a[i], where a evaluates to a list and i
    evaluates to an integer.
    
    """
    def __init__(self, expr1, expr2):
        super(ArrayIdxExpr1, self).__init__()
        assert isinstance(expr1, AExpr) and isinstance(expr2, AExpr)
        self.expr1 = expr1
        self.expr2 = expr2

    def __repr__(self):
        return "ArrayIdxExpr1(%s,%s)" % (repr(self.expr1), repr(self.expr2))

    def __str__(self):
        return "%s[%s]" % (str(self.expr1), str(self.expr2)+"-1")

    def __eq__(self, other):
        return isinstance(other, ArrayIdxExpr) and self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("ArrayIdx", self.expr1, self.expr2))

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def subst(self, inst):
        return ArrayIdxExpr(expr1=self.expr1.subst(inst), expr2=self.expr2.subst(inst))


class FieldNameExpr(AExpr):
    """Expression of the form a.name, where a evaluates to a structure
    and name is a field name.

    """
    def __init__(self, expr, field):
        super(FieldNameExpr, self).__init__()
        assert isinstance(expr, AExpr) and isinstance(field, str)
        self.expr = expr
        self.field = field

    def __repr__(self):
        return "FieldNameExpr(%s,%s)" % (repr(self.expr), self.field)

    def __str__(self):
        return "%s.%s" % (str(self.expr), self.field)

    def __eq__(self, other):
        return isinstance(other, FieldNameExpr) and self.expr == other.expr and \
            self.field == other.field

    def __hash__(self):
        return hash(("FieldName", self.expr, self.field))

    def get_vars(self):
        return self.expr.get_vars()

    def subst(self, inst):
        return FieldNameExpr(expr=self.expr.subst(inst), field=self.field)

    
class BExpr:
    def __init__(self):
        pass

    def get_vars(self):
        raise NotImplementedError

    def subst(self, inst):
        raise NotImplementedError


class BConst(BExpr):  # Boolean expression
    def __init__(self, value):
        super(BConst, self).__init__()
        assert isinstance(value, bool)
        self.value = value

    def __repr__(self):
        return "BConst(%s)" % str(self.value)

    def __str__(self):
        return "true" if self.value else "false"

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
        super(LogicExpr, self).__init__()
        assert op in ["&&", "||", "-->", "<-->"]
        # assert isinstance(expr1, BExpr) and isinstance(expr2, BExpr)
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2

    def __repr__(self):
        return "Logic(%s, %s, %s)" % (self.op, repr(self.expr1), repr(self.expr2))

    def __str__(self):
        expr1 = str(self.expr1)
        expr2 = str(self.expr2)
        if self.op in ["-->", "<-->"] and isinstance(self.expr2, LogicExpr) and self.expr2.op in ["-->", "<-->"]:
            expr2 = "(" + expr2 + ")"
        elif self.op == "&&":
            if isinstance(self.expr1, LogicExpr) and self.expr1.op != self.op:
                expr1 = "(" + expr1 + ")"
            if isinstance(self.expr2, LogicExpr) and self.expr2.op != self.op:
                expr2 = "(" + expr2 + ")"
        elif self.op == "||":
            if isinstance(self.expr1, LogicExpr) and self.expr1.op in ["-->", "<-->"]:
                expr1 = "(" + expr1 + ")"
            if isinstance(self.expr2, LogicExpr) and self.expr2.op in ["-->", "<-->"]:
                expr2 = "(" + expr2 + ")"
        return expr1 + " " + self.op + " " + expr2

    def __eq__(self, other):
        return isinstance(other, LogicExpr) and self.op == other.op and \
            self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("Logic", self.op, self.expr1, self.expr2))

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def subst(self, inst):
        return LogicExpr(self.op, self.expr1.subst(inst), self.expr2.subst(inst))


def list_conj(*args):
    if len(args) == 0:
        return true_expr
    if len(args) == 1:
        return args[0]
    return LogicExpr("&&", args[0], list_conj(*args[1:]))

def conj(*args):
    assert isinstance(args, tuple) and all(isinstance(arg, BExpr) for arg in args)
    if false_expr in args:
        return false_expr
    new_args = []
    for arg in args:
        if arg != true_expr and arg not in new_args:
            new_args.append(arg)
    return list_conj(*new_args)

def split_conj(e):
    if isinstance(e, LogicExpr) and e.op == '&&':
        return split_conj(e.expr1) + split_conj(e.expr2)
    else:
        return [e]

def list_disj(*args):
    if len(args) == 0:
        return false_expr
    if len(args) == 1:
        return args[0]
    return LogicExpr("||", args[0], list_disj(*args[1:]))

def disj(*args):
    assert isinstance(args, tuple) and all(isinstance(arg, BExpr) for arg in args)
    if true_expr in args:
        return true_expr
    new_args = []
    for arg in args:
        if arg != false_expr and arg not in new_args:
            new_args.append(arg)
    return list_disj(*new_args)
def split_disj(e):
    if isinstance(e, LogicExpr) and e.op == '||':
        return [e.expr1] + split_disj(e.expr2)
    else:
        return [e]


def imp(b1, b2):
    if b1 == false_expr or b2 == true_expr:
        return true_expr
    if b1 == true_expr:
        return b2
    return LogicExpr("-->", b1, b2)


class RelExpr(BExpr):
    neg_table = {"<": ">=", ">": "<=", "==": "!=", "!=": "==", ">=": "<", "<=": ">"}

    def __init__(self, op, expr1, expr2):
        super(RelExpr, self).__init__()
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
        self.mu_ex_conds = list()  # record a list of sets of mutually exclusive constraints

    def __repr__(self):
        def repr_pair(cond, inst):
            return "(%s, %s)" % (str(cond), str(inst))

        def repr_cond_inst(cond_inst):
            return "[" + ", ".join(repr_pair(cond, inst) for cond, inst in cond_inst) + "]"

        return "\n".join(var + ": " + repr_cond_inst(cond_inst) for var, cond_inst in self.data.items())

    def conflicting(self, conditions):
        assert isinstance(conditions, set)
        if len(conditions) == 0:
            return False  # No conflict
        elif len(conditions) == 1:
            condition = list(conditions)[0]
            if condition == false_expr:
                return True  # Conflict
            else:
                return False  # No conflict

        for cond0, cond1 in itertools.combinations_with_replacement(conditions, 2):
            if cond0 != cond1:
                for mu_ex_cond_set in self.mu_ex_conds:
                    if {cond0, cond1}.issubset(mu_ex_cond_set):
                        return True
        return False

    def add(self, var_name, cond_inst):
        """Add a new instantiation."""
        assert var_name not in self.data
        
        # Substitute using existing instantiations
        for var in self.data:
            new_cond_inst = []
            for cond, expr in cond_inst:
                if var in cond.get_vars() or var in expr.get_vars():
                    for cond_var, expr_var in self.data[var]:
                        new_cond = cond.subst({var: expr_var})
                        if self.conflicting({new_cond, cond_var}) or conj(new_cond, cond_var) == false_expr:
                            continue  # because new_cond && cond_var is False
                        else:
                            new_cond = conj(new_cond, cond_var)
                        new_expr = expr.subst({var: expr_var})
                        new_cond_inst.append((new_cond, new_expr))
                else:
                    new_cond_inst.append((cond, expr))
            cond_inst = new_cond_inst
        # Check: the conditons in cond_inst are different
        conditions = [cond for cond, _ in cond_inst]
        assert len(conditions) == len(set(conditions))

        # Merge (cond, expr) pairs with the same expression
        expr_dict = dict()
        for cond, expr in cond_inst:
            if expr not in expr_dict:
                expr_dict[expr] = []
            expr_dict[expr].append(cond)

        cond_inst = []
        for expr, conds in sorted(expr_dict.items(), key=str):
            cond_inst.append((disj(*conds), expr))

        self.data[var_name] = cond_inst

        # Extract mutually exclusive constraints
        if len(cond_inst) >= 2:
            mu_ex_cons = set(cond for cond, _ in cond_inst)
            if mu_ex_cons not in self.mu_ex_conds:
                self.mu_ex_conds.append(mu_ex_cons)


# add by lqq
# Modified by xux
class NegExpr(BExpr):
    def __init__(self, expr):
        super(NegExpr, self).__init__()
        assert isinstance(expr, BExpr)
        self.op = '~'
        self.expr = expr

    def __repr__(self):
        return "Not(%s)" % repr(self.expr)

    def __str__(self):
        return "~(" + str(self.expr) + ")"

    def __eq__(self, other):
        return isinstance(other, NegExpr) and self.op == other.op and self.expr == other.expr

    def __hash__(self):
        return hash(("Not", self.op, self.expr))

    def get_vars(self):
        return self.expr.get_vars()

    def subst(self, inst):
        # return NegExpr(self.op, self.expr.subst(inst))
        return NegExpr(self.expr.subst(inst))  # Probably?
