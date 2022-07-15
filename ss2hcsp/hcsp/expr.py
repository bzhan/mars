"""Expressions"""

import math
from decimal import Decimal
from fractions import Fraction
import itertools

from ss2hcsp.util.topsort import topological_sort


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


class Expr:
    """Arithmetic expression."""
    def __init__(self):
        pass

    def priority(self):
        """Returns priority during printing."""
        raise NotImplementedError

    def get_vars(self):
        """Returns set of variables in the expression."""
        raise NotImplementedError

    def get_fun_names(self):
        """Return set of function names in the expression"""
        return NotImplementedError

    def get_zero_arity_funcs(self):
        """Return set of functions with zero arity in the expression"""
        return NotImplementedError

    def subst(self, inst):
        """inst is a dictionary mapping variable names to expressions."""
        raise NotImplementedError


class AVar(Expr):
    def __init__(self, name, meta=None):
        super(AVar, self).__init__()
        assert isinstance(name, str)
        self.name = name
        self.meta = meta

    def __repr__(self):
        return "AVar(%s)" % self.name

    def __str__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, AVar) and self.name == other.name

    def __hash__(self):
        return hash(("AVar", self.name))

    def priority(self):
        return 100

    def get_vars(self):
        return {self.name}

    def get_fun_names(self):
        return set()

    def get_zero_arity_funcs(self):
        return set()

    def subst(self, inst):
        if self.name in inst:
            return inst[self.name]
        else:
            return self


class AConst(Expr):
    def __init__(self, value, meta=None):
        super(AConst, self).__init__()
        assert isinstance(value, (int, float, Decimal, Fraction, list, str, tuple, dict))
        # if isinstance(value, Decimal):
        #     value = float(value)
        self.value = value
        self.meta = meta

    def __repr__(self):
        return "AConst(%s)" % str_of_val(self.value)

    def __str__(self):
        return str_of_val(self.value)

    def __eq__(self, other):
        return isinstance(other, AConst) and self.value == other.value

    def __hash__(self):
        return hash(("AConst", str(self.value)))

    def priority(self):
        return 100

    def get_vars(self):
        return set()

    def get_fun_names(self):
        return set()

    def get_zero_arity_funcs(self):
        return set()

    def subst(self, inst):
        return self


class OpExpr(Expr):
    def __init__(self, op, *exprs, meta=None):
        super(OpExpr, self).__init__()
        assert op in ('+', '-', '*', '/', '%', '^')
        for expr in exprs:
            if not isinstance(expr, Expr):
                raise AssertionError
        # assert all(isinstance(expr, Expr) for expr in exprs)
        assert len(exprs) > 0 and len(exprs) <= 2, \
            "OpExpr: wrong number of arguments for %s" % op
        if len(exprs) == 1:
            assert op == '-', 'OpExpr: wrong number of arguments for %s' % op
        self.op = op
        self.exprs = tuple(exprs)
        self.meta = meta

    def __repr__(self):
        return "OpExpr(%s,%s)" % (repr(self.op), repr(self.exprs))
    
    def __str__(self):
        if len(self.exprs) == 1:
            assert self.op == '-'
            s = str(self.exprs[0])
            if self.exprs[0].priority() < self.priority():
                s = '(' + s + ')'
            return '-' + s
        else:
            s1, s2 = str(self.exprs[0]), str(self.exprs[1])
            if self.exprs[0].priority() < self.priority():
                s1 = '(' + s1 + ')'
            if self.exprs[1].priority() <= self.priority():
                s2 = '(' + s2 + ')'
            if self.op == '^':
                return s1 + self.op + s2
            else:
                return s1 + ' ' + self.op + ' ' + s2

    def __eq__(self, other):
        return isinstance(other, OpExpr) and self.op == other.op and self.exprs == other.exprs

    def __hash__(self):
        return hash(("OpExpr", self.op, self.exprs))

    def priority(self):
        if len(self.exprs) == 1:
            return 80
        elif self.op == '^':
            return 85
        elif self.op == '*' or self.op == '/' or self.op == '%':
            return 70
        else:
            return 65

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def get_fun_names(self):
        return set().union(*(expr.get_fun_names() for expr in self.exprs))

    def get_zero_arity_funcs(self):
        return set().union(*(expr.get_zero_arity_funcs() for expr in self.exprs))

    def subst(self, inst):
        return OpExpr(self.op, *(expr.subst(inst) for expr in self.exprs))

def list_add(*args):
    if len(args) == 0:
        return 0
    elif len(args) == 1:
        return args[0]
    else:
        return OpExpr('+', args[0], list_add(*args[1:]))

def list_mul(*args):
    if len(args) == 0:
        return 1
    elif len(args) == 1:
        return args[0]
    else:
        return OpExpr('*', args[0], list_mul(*args[1:]))

class FunExpr(Expr):
    def __init__(self, fun_name, exprs, meta=None):
        super(FunExpr, self).__init__()
        self.fun_name = fun_name
        assert isinstance(self.fun_name, str)
        exprs = tuple(exprs)
        assert all(isinstance(expr, Expr) for expr in exprs)
        self.exprs = exprs
        self.meta = meta

    def __repr__(self):
        return "Fun(%s, %s)" % (self.fun_name, ", ".join(repr(expr) for expr in self.exprs))

    def __str__(self):
        return "%s(%s)" % (self.fun_name, ",".join(str(expr) for expr in self.exprs))

    def __eq__(self, other):
        return isinstance(other, FunExpr) and self.fun_name == other.fun_name and \
               self.exprs == other.exprs

    def __hash__(self):
        return hash(("Fun", self.fun_name, self.exprs))

    def priority(self):
        return 100

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def get_fun_names(self):
        func_names = set((self.fun_name,))
        return func_names.union(*(expr.get_fun_names() for expr in self.exprs))

    def get_zero_arity_funcs(self):
        if len(self.exprs) == 0:
            zero_arity_funcs = set((self.fun_name + '(' + ')',))
        return zero_arity_funcs.union(*(expr.get_zero_arity_funcs() for expr in self.exprs))

    def subst(self, inst):
        return FunExpr(self.fun_name, [expr.subst(inst) for expr in self.exprs])


class IfExpr(Expr):
    def __init__(self, cond, expr1, expr2, meta=None):
        super(IfExpr, self).__init__()
        assert isinstance(cond, Expr) and isinstance(expr1, Expr) and isinstance(expr2, Expr)
        self.cond = cond
        self.expr1 = expr1
        self.expr2 = expr2
        self.meta = meta
    
    def __repr__(self):
        return "IfExpr(%s,%s,%s)" % (repr(self.cond), repr(self.expr1), repr(self.expr2))
    
    def __str__(self):
        s0, s1, s2 = str(self.cond), str(self.expr1), str(self.expr2)
        return "(%s ? %s : %s)" % (s0, s1, s2)

    def __eq__(self, other):
        return isinstance(other, IfExpr) and self.cond == other.cond and \
            self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("IfExpr", self.cond, self.expr1, self.expr2))

    def priority(self):
        return 100

    def get_vars(self):
        return set().union(*(arg.get_vars() for arg in [self.cond, self.expr1, self.expr2]))

    def get_fun_names(self):
        return set().union(*(arg.get_fun_names() for arg in [self.cond, self.expr1, self.expr2]))

    def get_zero_arity_funcs(self):
        return set().union(*(arg.get_zero_arity_funcs() for arg in [self.cond, self.expr1, self.expr2]))
    
    def subst(self, inst):
        return IfExpr(self.cond.subst(inst), self.expr1.subst(inst), self.expr2.subst(inst))


class ListExpr(Expr):
    """List expressions."""
    def __init__(self, *args, meta=None):
        super(ListExpr, self).__init__()
        args = tuple(args)
        assert all(isinstance(arg, Expr) for arg in args)
        self.args = args
        self.count = 0
        self.meta = meta

    def __repr__(self):
        return "List(%s)" % (','.join(repr(arg) for arg in self.args))

    def __str__(self):
        return "[%s]" % (','.join(str(arg) for arg in self.args))

    def __eq__(self, other):
        return isinstance(other, ListExpr) and self.args == other.args

    def __hash__(self):
        return hash(("ListExpr", self.args))

    def priority(self):
        return 100

    def get_vars(self):
        return set().union(*(arg.get_vars() for arg in self.args))

    def get_fun_names(self):
        return set().union(*(arg.get_fun_names() for arg in self.args))

    def get_zero_arity_funcs(self):
        return set().union(*(arg.get_zero_arity_funcs() for arg in self.args))

    def subst(self, inst):
        return ListExpr(*(expr.subst(inst) for expr in self.args))


class DictExpr(Expr):
    """Dictionary expressions (structures)."""
    def __init__(self, *args, meta=None):
        """Argument is a list of key-value pairs. Each key should be a string."""
        super(DictExpr, self).__init__()
        self.dict = dict()
        args = tuple(args)
        assert all(isinstance(k, str) and isinstance(v, Expr) for k, v in args)
        for k, v in args:
            self.dict[k] = v
        self.meta = meta

    def __repr__(self):
        return "Dict(%s)" % (','.join(k + ':' + repr(v) for k, v in self.dict.items()))

    def __str__(self):
        return "{%s}" % (','.join(k + ':' + str(v) for k, v in self.dict.items()))

    def __eq__(self, other):
        return isinstance(other, DictExpr) and self.dict == other.dict

    def __hash__(self):
        return hash(("Dict", tuple((k, v) for k, v in self.dict.items())))

    def priority(self):
        return 100

    def get_vars(self):
        return set().union(*(v.get_vars() for k, v in self.dict.items()))

    def get_fun_names(self):
        return set().union(*(v.get_fun_names() for k, v in self.dict.items()))

    def get_zero_arity_funcs(self):
        return set().union(*(v.get_zero_arity_funcs() for k, v in self.dict.items()))

    def subst(self, inst):
        return DictExpr(*((k, v.subst(inst)) for k, v in self.dict.items()))


class ArrayIdxExpr(Expr):
    """Expressions of the form a[i], where a evaluates to a list and i
    evaluates to an integer. Constructor also supports the case where the
    second argument is a list.
    
    """
    def __init__(self, expr1, expr2, meta=None):
        super(ArrayIdxExpr, self).__init__()
        if isinstance(expr1, str):
            expr1 = AVar(expr1)
        assert isinstance(expr1, Expr)
        if isinstance(expr2, Expr):
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
        self.meta = meta

    def __repr__(self):
        return "ArrayIdxExpr(%s,%s)" % (repr(self.expr1), repr(self.expr2))

    def __str__(self):
        return "%s[%s]" % (str(self.expr1), str(self.expr2))

    def __eq__(self, other):
        return isinstance(other, ArrayIdxExpr) and self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("ArrayIdx", self.expr1, self.expr2))

    def priority(self):
        return 100

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def get_fun_names(self):
        return self.expr1.get_fun_names().union(self.expr2.get_fun_names())

    def get_zero_arity_funcs(self):
        return self.expr1.get_zero_arity_funcs().union(self.expr2.get_zero_arity_funcs())

    def subst(self, inst):
        return ArrayIdxExpr(expr1=self.expr1.subst(inst), expr2=self.expr2.subst(inst))


class FieldNameExpr(Expr):
    """Expression of the form a.name, where a evaluates to a structure
    and name is a field name.

    """
    def __init__(self, expr, field, meta=None):
        super(FieldNameExpr, self).__init__()
        assert isinstance(expr, Expr) and isinstance(field, str)
        self.expr = expr
        self.field = field
        self.meta = meta

    def __repr__(self):
        return "FieldNameExpr(%s,%s)" % (repr(self.expr), self.field)

    def __str__(self):
        return "%s.%s" % (str(self.expr), self.field)

    def __eq__(self, other):
        return isinstance(other, FieldNameExpr) and self.expr == other.expr and \
            self.field == other.field

    def __hash__(self):
        return hash(("FieldName", self.expr, self.field))

    def priority(self):
        return 100

    def get_vars(self):
        return self.expr.get_vars()

    def get_fun_names(self):
        return self.expr.get_fun_names()

    def get_zero_arity_funcs(self):
        return self.expr.get_zero_arity_funcs()

    def subst(self, inst):
        return FieldNameExpr(expr=self.expr.subst(inst), field=self.field)

class BConst(Expr):  # Boolean expression
    def __init__(self, value, meta=None):
        super(BConst, self).__init__()
        assert isinstance(value, bool)
        self.value = value
        self.meta = meta

    def __repr__(self):
        return "BConst(%s)" % str(self.value)

    def __str__(self):
        return "true" if self.value else "false"

    def __eq__(self, other):
        return isinstance(other, BConst) and self.value == other.value

    def __hash__(self):
        return hash(("BConst", self.value))

    def priority(self):
        return 100

    def get_vars(self):
        return set()

    def get_fun_names(self):
        return set()

    def get_zero_arity_funcs(self):
        return set()

    def subst(self, inst):
        return self

true_expr = BConst(True)
false_expr = BConst(False)

class LogicExpr(Expr):
    def __init__(self, op, *exprs, meta=None):
        super(LogicExpr, self).__init__()
        assert op in ["&&", "||", "->", "<->", "!"]
        assert all(isinstance(expr, Expr) for expr in exprs), \
            "Expected Expr: {}".format(exprs)
        assert len(exprs) > 0 and len(exprs) <= 2, \
            "LogicExpr: wrong number of arguments for %s" % op
        if len(exprs) == 1:
            assert op == '!', "LogicExpr: wrong number of arguments for %s" % op
        self.op = op
        self.exprs = tuple(exprs)
        self.meta = meta

    def __repr__(self):
        return "Logic(%s,%s)" % (repr(self.op), repr(self.exprs))

    def __str__(self):
        if len(self.exprs) == 1:
            assert self.op == '!'
            s = str(self.exprs[0])
            if self.exprs[0].priority() < self.priority():
                s = '(' + s + ')'
            return '!' + s
        else:
            s1, s2 = str(self.exprs[0]), str(self.exprs[1])
            if self.exprs[0].priority() <= self.priority():
                s1 = '(' + s1 + ')'
            if self.exprs[1].priority() < self.priority():
                s2 = '(' + s2 + ')'
            return s1 + ' ' + self.op + ' ' + s2

    def __eq__(self, other):
        return isinstance(other, LogicExpr) and self.op == other.op and self.exprs == other.exprs

    def __hash__(self):
        return hash(("Logic", self.op, self.exprs))

    def priority(self):
        if self.op == '<->':
            return 25
        elif self.op == '->':
            return 20
        elif self.op == '&&':
            return 35
        elif self.op == '||':
            return 30
        elif self.op == '!':
            return 40
        else:
            raise NotImplementedError

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def get_fun_names(self):
        return set().union(*(expr.get_fun_names() for expr in self.exprs))

    def get_zero_arity_funcs(self):
        return set().union(*(expr.get_zero_arity_funcs() for expr in self.exprs))

    def subst(self, inst):
        return LogicExpr(self.op, *(expr.subst(inst) for expr in self.exprs))


def list_conj(*args):
    if len(args) == 0:
        return true_expr
    if len(args) == 1:
        return args[0]
    return LogicExpr("&&", args[0], list_conj(*args[1:]))

def conj(*args):
    """Form the conjunction of the list of arguments.
    
    Example: conj("x > 1", "x < 3") forms "x > 1 && x < 3"

    """
    assert isinstance(args, tuple) and all(isinstance(arg, Expr) for arg in args)
    if false_expr in args:
        return false_expr
    new_args = []
    for arg in args:
        if arg != true_expr and arg not in new_args:
            new_args.append(arg)
    return list_conj(*new_args)

def split_conj(e):
    if isinstance(e, LogicExpr) and e.op == '&&':
        return split_conj(e.exprs[0]) + split_conj(e.exprs[1])
    else:
        return [e]

def list_disj(*args):
    if len(args) == 0:
        return false_expr
    if len(args) == 1:
        return args[0]
    return LogicExpr("||", args[0], list_disj(*args[1:]))

def disj(*args):
    """Form the disjunction of the list of arguments.
    
    Example: disj("x > 1", "x < 3") forms "x > 1 || x < 3"

    """
    assert isinstance(args, tuple) and all(isinstance(arg, Expr) for arg in args)
    if true_expr in args:
        return true_expr
    new_args = []
    for arg in args:
        if arg != false_expr and arg not in new_args:
            new_args.append(arg)
    return list_disj(*new_args)

def split_disj(e):
    if isinstance(e, LogicExpr) and e.op == '||':
        return [e.exprs[0]] + split_disj(e.exprs[1])
    else:
        return [e]

def imp(b1, b2):
    if b1 == false_expr or b2 == true_expr:
        return true_expr
    if b1 == true_expr:
        return b2
    return LogicExpr("->", b1, b2)
    

class RelExpr(Expr):
    neg_table = {"<": ">=", ">": "<=", "==": "!=", "!=": "==", ">=": "<", "<=": ">"}

    def __init__(self, op, expr1, expr2, meta=None):
        super(RelExpr, self).__init__()
        assert op in ["<", ">", "==", "!=", ">=", "<="]
        assert isinstance(expr1, Expr) and isinstance(expr2, Expr)
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2
        self.meta = meta

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
        if self.op == "==":
            return disj(RelExpr(">", self.expr1, self.expr2), RelExpr("<", self.expr1, self.expr2))
        return RelExpr(RelExpr.neg_table[self.op], self.expr1, self.expr2)

    def priority(self):
        return 50

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def get_fun_names(self):
        return self.expr1.get_fun_names().union(self.expr2.get_fun_names())

    def get_zero_arity_funcs(self):
        return self.expr1.get_zero_arity_funcs().union(self.expr2.get_zero_arity_funcs())

    def subst(self, inst):
        return RelExpr(self.op, self.expr1.subst(inst), self.expr2.subst(inst))

class ExistsExpr(Expr):
    """Exists expressions"""
    def __init__(self, vars, expr, meta=None):
        assert isinstance(expr, Expr)
        if isinstance(vars, str):
            vars = AVar(vars)
        elif isinstance(vars, list):
            assert all(isinstance(var, str) for var in vars)
            vars = tuple(AVar(var) for var in vars)
        assert isinstance(vars, (AVar, tuple))
        self.vars = vars
        self.expr = expr
        self.meta = meta

    def __repr__(self):
        if isinstance(self.vars, AVar):
            return "ExistsExpr(%s, %s)" % (repr(self.vars), repr(self.expr))
        else:
            return "ExistsExpr({%s}, %s)" % ((', '.join(repr(var) for var in self.vars)), repr(self.expr))

    def __str__(self):
        if isinstance(self.vars, AVar):
            return "EX %s. %s" % (str(self.vars), str(self.expr))
        else:
            return "EX {%s}. %s" % ((', '.join(str(var) for var in self.vars)), str(self.expr))

    def __eq__(self, other):
        # Currently does not consider alpha equivalence.
        return isinstance(other, ExistsExpr) and self.vars == other.vars and self.expr == other.expr

    def __hash__(self):
        return hash(("Exists", self.vars, self.expr))

    def priority(self):
        return 10

    def get_vars(self):
        # Currently also include the bound variable.
        return self.expr.get_vars()

    def get_fun_names(self):
        return self.expr.get_fun_names()

    def get_zero_arity_funcs(self):
        return self.expr.get_zero_arity_funcs()

    def subst(self, inst):
        # Currently assume the bound variable cannot be substituded.
        assert self.vars not in inst
        return ExistsExpr(self.vars, self.expr.subst(inst))

class ForAllExpr(Expr):
    """ForAll expressions"""
    def __init__(self, vars, expr, meta=None):
        assert isinstance(expr, Expr)
        if isinstance(vars, str):
            vars = AVar(vars)
        elif isinstance(vars, list):
            assert all(isinstance(var, str) for var in vars)
            vars = tuple(AVar(var) for var in vars)
        assert isinstance(vars, (AVar, tuple))
        self.vars = vars
        self.expr = expr
        self.meta = meta

    def __repr__(self):
        if isinstance(self.vars, AVar):
            return "ForAllExpr(%s, %s)" % (repr(self.vars), repr(self.expr))
        else:
            return "ForAllExpr({%s}, %s)" % ((', '.join(repr(var) for var in self.vars)), repr(self.expr))

    def __str__(self):
        if isinstance(self.vars, AVar):
            return "ForAll %s. %s" % (str(self.vars), str(self.expr))
        else:
            return "ForAll {%s}. %s" % ((', '.join(str(var) for var in self.vars)), str(self.expr))

    def __eq__(self, other):
        # Currently does not consider alpha equivalence.
        return isinstance(other, ForAllExpr) and self.vars == other.vars and self.expr == other.expr

    def __hash__(self):
        return hash(("ForAll", self.vars, self.expr))

    def priority(self):
        return 10

    def get_vars(self):
        # Currently also include the bound variable.
        return self.expr.get_vars()

    def get_fun_names(self):
        return self.expr.get_fun_names()
    
    def get_zero_arity_funcs(self):
        return self.expr.get_zero_arity_funcs()
    
    def subst(self, inst):
        # Currently assume the bound variable cannot be substituded.
        assert self.vars not in inst
        return ForAllExpr(self.vars, self.expr.subst(inst))

def neg_expr(e):
    """Returns the negation of an expression, using deMorgan's law to move
    negation inside.

    """
    if e == true_expr:
        return false_expr
    elif e == false_expr:
        return true_expr
    elif isinstance(e, LogicExpr):
        if e.op == '&&':
            return LogicExpr('||', neg_expr(e.exprs[0]), neg_expr(e.exprs[1]))
        elif e.op == '||':
            return LogicExpr('&&', neg_expr(e.exprs[0]), neg_expr(e.exprs[1]))
        elif e.op == '->':
            return LogicExpr('&&', e.exprs[0], neg_expr(e.exprs[1]))
        elif e.op == '<->':
            return LogicExpr('<->', e.exprs[0], neg_expr(e.exprs[1]))
        elif e.op == '!':
            return e.exprs[0]
        else:
            raise NotImplementedError
    elif isinstance(e, RelExpr):
        return e.neg()
    else:
        raise NotImplementedError

def subst_all(e, inst):
    """Perform all substitutions given in inst. Detect cycles.
    
    First compute a topological sort of dependency in inst, which will
    provide the order of substitution.

    """
    # Set of all variables to be substituted
    all_vars = set(inst.keys())

    # Mapping variable to its dependencies
    dep_order = dict()
    for var in all_vars:
        dep_order[var] = list(inst[var].get_vars().intersection(all_vars))

    topo_order = topological_sort(dep_order)
    for var in reversed(topo_order):
        e = e.subst({var: inst[var]})
    return e


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
                            continue  # because new_cond & cond_var is False
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
