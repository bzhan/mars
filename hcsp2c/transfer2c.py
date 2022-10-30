"""transfer HCSP to C programs, return str"""

from decimal import Decimal
from fractions import Fraction
from typing import List

from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.hcsp import HCSPInfo, Procedure


gl_var_type = {} # key: var_name, value:type,  0 -> undef, 1 -> double, 2 -> string, 3 -> list

def indent(s: str) -> str:
    lines = s.split('\n')
    lines = ['    ' + line for line in lines]
    return '\n'.join(lines)

class TypeContext:
    def __init__(self):
        # Mapping from channel names to types
        self.channelTypes = dict()

        # Mapping from process name to mapping of variable to types
        self.varTypes = dict()

    def __str__(self):
        res = ""
        for ch_name, typ in self.channelTypes.items():
            res += "%s -> %s\n" % (ch_name, typ)
        for hp_name, varctx in self.varTypes.items():
            res += hp_name + ":\n"
            for var_name, typ in varctx.items():
                res += "  %s -> %s\n" % (var_name, typ)
        return res


class CType:
    pass

class UndefType(CType):
    def __str__(self):
        return "undef"

class NullType(CType):
    def __str__(self):
        return "null"

class RealType(CType):
    def __str__(self):
        return "double"

class StringType(CType):
    def __str__(self):
        return "string"

class ListType(CType):
    def __str__(self):
        return "list"


def inferExprType(e: expr.Expr, hp_name: str, ctx: TypeContext) -> CType:
    """Infer type of expression under the given context."""
    if isinstance(e, expr.AVar):
        if e.name in ctx.varTypes[hp_name]:
            return ctx.varTypes[hp_name][e.name]
        else:
            return UndefType()
    elif isinstance(e, expr.AConst):
        if isinstance(e.value, (int, float, Decimal, Fraction)):
            return RealType()
        elif isinstance(e.value, str):
            return StringType()
        else:
            raise NotImplementedError
    elif isinstance(e, expr.ListExpr):
        return ListType()
    elif isinstance(e, expr.IfExpr):
        return inferExprType(e.expr1, hp_name, ctx)
    elif isinstance(e, expr.OpExpr):
        return RealType()
    elif isinstance(e, expr.FunExpr):
        if e.fun_name in ('max', 'min', 'len'):
            return RealType()
        elif e.fun_name in ('push', 'pop', 'get', 'del0', 'get_max', 'del'):
            return ListType()
        # elif e.fun_name in ('bottom', 'top'): # not really
        #     return RealType()
        else:
            # print("inferExprType: unrecognized function %s" % e.fun_name)
            return UndefType()
            # raise NotImplementedError
    elif isinstance(e, expr.ArrayIdxExpr):
        return UndefType()
    else:
        print("inferExprType on %s" % e)
        raise NotImplementedError

def inferTypes(infos: List[HCSPInfo]) -> TypeContext:
    """Infer type of channel and variables.
    
    Input is a list of (name, hp) pairs.

    """
    ctx = TypeContext()
    for info in infos:
        ctx.varTypes[info.name] = dict()

    def infer(hp_name, hp) -> int:
        flag = 0
        if isinstance(hp, hcsp.Assign):
            v = hp.var_name
            if isinstance(v, expr.AVar):
                if v.name in ctx.varTypes[hp_name] and not isinstance(ctx.varTypes[hp_name][v.name], UndefType):
                    pass   # Already know type of v, skip type checking
                else:
                    typ = inferExprType(hp.expr, hp_name, ctx)
                    if isinstance(typ, UndefType):
                        ctx.varTypes[hp_name][v.name] = typ
                        # raise AssertionError("inferTypes: unknown type for right side of assignment")
                    else:
                        ctx.varTypes[hp_name][v.name] = typ
                        flag = 1
            else:
                pass  # skip type inference for arrays and fields

        elif isinstance(hp, hcsp.InputChannel):
            ch = hp.ch_name
            
            if ch.name in ctx.channelTypes and not isinstance(ctx.channelTypes[ch.name], UndefType):
                v = hp.var_name
                if isinstance(v, expr.AVar):
                    if v.name not in ctx.varTypes[hp_name] or isinstance(ctx.varTypes[hp_name][v.name], UndefType):
                        ctx.varTypes[hp_name][v.name] = ctx.channelTypes[ch.name]
                        flag = 1
                    else:
                        pass  # Already know type of ch and v, skip type checking
                elif v is None:
                    ctx.channelTypes[ch.name] = NullType()
                else:
                    print(str(v))
                    raise NotImplementedError
            elif hp.var_name is None:
                ctx.channelTypes[ch.name] = NullType()
                flag = 1
            else:
                v = hp.var_name
                if isinstance(v, expr.AVar):
                    if v.name in ctx.varTypes[hp_name] and not isinstance(ctx.varTypes[hp_name][v.name], UndefType):
                        ctx.channelTypes[ch.name] = ctx.varTypes[hp_name][v.name]
                        flag = 1
                    else:
                        ctx.channelTypes[ch.name] = UndefType()
                        # raise AssertionError("inferTypes: unknown type for input variable %s", v.name)
                else:
                    raise NotImplementedError
        
        elif isinstance(hp, hcsp.OutputChannel):
            ch = hp.ch_name
            
            if ch.name in ctx.channelTypes and not isinstance(ctx.channelTypes[ch.name], UndefType):
                pass  # Already know type of ch, skip type checking
            elif hp.expr is None:
                ctx.channelTypes[ch.name] = NullType()
                flag = 1
            else:
                e = hp.expr
                typ = inferExprType(e, hp_name, ctx)
                if isinstance(typ, UndefType):
                    ctx.channelTypes[ch.name] = typ
                    # raise AssertionError("inferTypes: unknown type for output expression %s", e)
                else:
                    ctx.channelTypes[ch.name] = typ
                    flag = 1
        
        elif isinstance(hp, (hcsp.ODE_Comm, hcsp.SelectComm)):
            for io_comm, out_hp in hp.io_comms:
                mid_flag = infer(hp_name, io_comm)
                if mid_flag == 1:
                    flag = 1
                if out_hp is not None:
                    mid_flag = infer(hp_name, out_hp)
                    if mid_flag == 1:
                        flag = 1

        elif isinstance(hp, hcsp.Sequence):
            for sub_hp in hp.hps:
                mid_flag = infer(hp_name, sub_hp)
                if mid_flag == 1:
                    flag = 1

        elif isinstance(hp, hcsp.ITE):
            for _, if_hp in hp.if_hps:
                mid_flag = infer(hp_name, if_hp)
                if mid_flag == 1:
                    flag = 1
            if hp.else_hp is not None:
                mid_flag = infer(hp_name, hp.else_hp)
                if mid_flag == 1:
                    flag = 1

        elif isinstance(hp, hcsp.Loop):
            mid_flag = infer(hp_name, hp.hp)
            if mid_flag == 1:
                    flag = 1

        else:
            pass  # No need for type inference on other commands
        return flag

    flag = 0
    count = 0
    for info in infos:
        flag += infer(info.name, info.hp)
        for procedure in info.procedures:
            flag += infer(info.name, procedure.hp)
    while flag > 0:
        count += 1
        print(count)
        print(flag)
        flag = 0
        for info in infos:
            flag += infer(info.name, info.hp)
            for procedure in info.procedures:
                flag += infer(info.name, procedure.hp)

    return ctx

def cPriority(e: expr.Expr) -> int:
    """Obtain the priority of expression when converted to C."""
    if isinstance(e, expr.AVar):
        return 100
    elif isinstance(e, expr.AConst):
        return 100
    elif isinstance(e, expr.OpExpr):
        if len(e.exprs) == 1:
            return 80
        elif e.op == '^':
            return 100
        elif e.op in ('*', '/', '%'):
            return 70
        else:
            return 65
    elif isinstance(e, expr.RelExpr):
        return 50
    elif isinstance(e, expr.IfExpr):
        return 100
    elif isinstance(e, expr.LogicExpr):
        if e.op == '<->':
            return 25
        elif e.op == '->':
            return 20
        elif e.op == '&&':
            return 35
        elif e.op == '||':
            return 30
        elif e.op == '!':
            return 40
    elif isinstance(e, expr.FunExpr):
        return 100
    elif isinstance(e, expr.ListExpr):
        return 100
    elif isinstance(e, expr.ArrayIdxExpr):
        return 100
    else:
        raise NotImplementedError


def transferToCExpr(e: expr.Expr) -> str:
    """Convert HCSP expression into C expression."""
    if isinstance(e, expr.AVar):
        return e.name
    elif isinstance(e, expr.OpExpr):
        if e.op == '-' and len(e.exprs) == 1:
            s = transferToCExpr(e.exprs[0])
            if cPriority(e.exprs[0]) < cPriority(e):
                s = '(' + s + ')'
            return '-' + s
        else:
            s1, s2 = transferToCExpr(e.exprs[0]), transferToCExpr(e.exprs[1])
            if cPriority(e.exprs[0]) < cPriority(e):
                s1 = '(' + s1 + ')'
            if cPriority(e.exprs[1]) <= cPriority(e):
                s2 = '(' + s2 + ')'
            if e.op in ('+', '-', '*', '/'):
                return "%s %s %s" % (s1, e.op, s2)
            elif e.op == '^':
                return "pow(%s, %s)" % (transferToCExpr(e.exprs[0]), transferToCExpr(e.exprs[1]))
            elif e.op == '%':
                return "(int) %s %% %s" % (s1, s2)
            else:
                print("transferToCExpr: %s" % e)
                raise NotImplementedError
    elif isinstance(e, expr.RelExpr):
        if e.op == "==":
            if isinstance(e.expr1, expr.AConst):
                mid = e.expr1
                e.expr1 = e.expr2
                e.expr2 = mid
            if isinstance(e.expr2, expr.AConst):
                if isinstance(e.expr2.value, str):
                    return "strEqual(%s, &strInit(%s))" % (e.expr1, e.expr2.value)
                elif isinstance(e.expr2, expr.AVar) and e.expr2.name in gl_var_type and isinstance(gl_var_type[e.expr2.name], StringType):
                    return "strEqual(%s, %s)" % (e.expr1, e.expr2)
                else:
                    s1, s2 = transferToCExpr(e.expr1), transferToCExpr(e.expr2)
                    if cPriority(e.expr1) < cPriority(e):
                        s1 = '(' + s1 + ')'
                    if cPriority(e.expr2) <= cPriority(e):
                        s2 = '(' + s2 + ')'
                    return "%s == %s" % (s1, s2)
        else:
            s1, s2 = transferToCExpr(e.expr1), transferToCExpr(e.expr2)
            if cPriority(e.expr1) < cPriority(e):
                s1 = '(' + s1 + ')'
            if cPriority(e.expr2) <= cPriority(e):
                s2 = '(' + s2 + ')'
            return "%s %s %s" % (s1, e.op, s2)
    elif isinstance(e, expr.AConst):
        if isinstance(e.value, str):
            return "*strInit(\"%s\")" % e.value
        else:
            return str(e.value)
    elif isinstance(e, expr.ListExpr):
        res = "midList = listInit();\n"
        for i in range(e.count):
            b = e.args[i]
            if isinstance(b, expr.AVar):
                if isinstance(gl_var_type[b.name], RealType):
                    res += "midList = listPush(midList, (void*)(&%s), 1)" % b
                elif isinstance(gl_var_type[b.name], StringType):
                    res += "midList = listPush(midList, (void*)(&%s), 2)" % b
                elif isinstance(gl_var_type[b.name], ListType):
                    res += "midList = listPush(midList, (void*)(&%s), 3)" % b
            elif isinstance(b, expr.AConst) and isinstance(b.value, str):
                res += "midList = listPush(midList, (void*)strInit(%s), 2)" % b
            elif isinstance(b, expr.ListExpr):
                raise AssertionError("cannot push a raw list to a list")
            else:
                res += "midList = listPushNum(midList, %s)" % b

        return res
    elif isinstance(e, expr.IfExpr):
        return "(%s ? %s : %s)" % (transferToCExpr(e.cond), transferToCExpr(e.expr1), transferToCExpr(e.expr2))
    elif isinstance(e, expr.LogicExpr):
        if e.op == '!':
            s = transferToCExpr(e.exprs[0])
            if cPriority(e.exprs[0]) < cPriority(e):
                s = '(' + s + ')'
            return "!%s" % s
        else:
            s1, s2 = transferToCExpr(e.exprs[0]), transferToCExpr(e.exprs[1])
            if cPriority(e.exprs[0]) < cPriority(e):
                s1 = '(' + s1 + ')'
            if cPriority(e.exprs[1]) <= cPriority(e):
                s2 = '(' + s2 + ')'
            return "(%s) %s (%s)" % (s1, e.op, s2)
    elif isinstance(e, expr.ArrayIdxExpr):
        return "listGet(&%s, %s)" % (e.expr1, e.expr2)
    elif isinstance(e, expr.FunExpr):
        # Special functions
        args = e.exprs
        cargs = [transferToCExpr(arg) for arg in args]

        if e.fun_name == "min":
            return "min(%d, %s)" % (len(args), ', '.join(cargs))
        elif e.fun_name == "max":
            return "max(%d, %s)" % (len(args), ', '.join(cargs))
        elif e.fun_name == "pi":
            return "PI"
        # elif e.fun_name == "abs":
        #     return abs(*args)
        # elif e.fun_name == "gcd":
        #     return math.gcd(*args)
        # elif e.fun_name == "div":
        #     a, b = args
        #     return int(a) // int(b)
        # elif e.fun_name == "sin":
        #     return math.sin(args[0])
        elif e.fun_name == "push":
            a, b = args
            if isinstance(b, expr.AVar):
                if isinstance(gl_var_type[b.name], RealType):
                    return "*listPush(&%s, (void*)(&%s), 1)" % (a, b)
                elif isinstance(gl_var_type[b.name], StringType):
                    return "*listPush(&%s, (void*)(&%s), 2)" % (a, b)
                elif isinstance(gl_var_type[b.name], ListType):
                    return "*listPush(&%s, (void*)(&%s), 3)" % (a, b)
            elif isinstance(b, expr.AConst) and isinstance(b.value, str):
                return "*listPush(&%s, (void*)strInit(%s), 2)" % (a, b)
            elif isinstance(b, expr.ListExpr):
                raise AssertionError("cannot push a raw list to a list")
            else:
                return "*listPushExpr(&%s, %s)" % (a, b)
        elif e.fun_name == "del":
            a, b = args
            return "*listDel(&%s, %s)" % (a, b)
        elif e.fun_name == "pop":
            a, = args
            return "*listPop(&%s)" % a
        elif e.fun_name == "top":
            a, = args
            return "listTop(&%s)" % a
        elif e.fun_name == "bottom":
            a, = args
            return "listBottom(&%s)" % a
        elif e.fun_name == "len":
            a, = args
            return "%s.length" % a
        elif e.fun_name == "get":
            a, = args
            return "*listPopBack(&%s)" % a
        elif e.fun_name == "get_max":
            a, = args
            return "listGetMaxList(&%s)" % a
        elif e.fun_name == "del0":
            a, b = args
            if isinstance(b, expr.AVar):
                if isinstance(gl_var_type[b.name], RealType):
                    return "*listDel0(&%s, (void*)(&%s), 1)" % (a, b)
                elif isinstance(gl_var_type[b.name], StringType):
                    return "*listDel0(&%s, (void*)(&%s), 2)" % (a, b)
                elif isinstance(gl_var_type[b.name], ListType):
                    return "*listDel0(&%s, (void*)(&%s), 3)" % (a, b)
            elif isinstance(b, expr.AConst) and isinstance(b.value, str):
                return "*listDel0(&%s, (void*)strInit(%s), 2)" % (a, b)
            else:
                raise AssertionError("del0 type error: %s %s" % (type(b), str(b)))
        else:
            print("transferToCExpr: unsupported function %s" % e.fun_name)
            raise NotImplementedError
    
    else:
        print("transferToCExpr:", e)
        raise NotImplementedError

c_procedure_template = \
"""
void %s () {
    %s
    return;
}
"""

def transferToCProcedure(procedure: Procedure) -> str:
    pro_info = HCSPInfo(procedure.name, procedure.hp)
    res = c_procedure_template % (procedure.name, indent(transferToC(pro_info)))
    return res

c_process_template = \
"""
void* %s (void* arg) {
    threadNumber = (int)(*((int*)arg));
    %s
    threadState[threadNumber] = STATE_STOPPED;
    updateCurrentTime(threadNumber);
    return NULL;
}"""

body_template = \
"""
#include <math.h>
#include "hcsp2c.h"
#include "%s.h"

static int threadNumber = 0;
static int midInt = 0;
static int is_comm = 0;
static String* midString = NULL;
static List* midList = NULL;
static Channel channel;
static Channel channels[%d];
static double h = step_size;
static double* midDouble = NULL;
"""

def transferToCProcess(name: str, info: HCSPInfo, context: TypeContext) -> str:
    """Convert HCSP process with given name to a C function"""
    c_process_str = ""
    global gl_var_type
    gl_var_type = context.varTypes[info.name]
    body = ""
    procedures_body = ""
    procedures = []
    for procedure in procedures:
        procedures_body += transferToCProcedure(procedure) + '\n'
    vars = info.hp.get_vars()
    init_body = body_template % (name, len(info.hp.get_chs()))
    for var in vars:
        if var not in context.varTypes[info.name]:
            raise AssertionError("type of %s in %s is unkonwn." % (var, info.name))
        if isinstance(context.varTypes[info.name][var], RealType):
            init_body += "\tstatic double %s = 0.0;\n" % var
        elif isinstance(context.varTypes[info.name][var], StringType):
            init_body += "\tstatic String %s;\n" % var
        elif isinstance(context.varTypes[info.name][var], ListType):
            init_body += "\tstatic List %s;\n" % var
        else:
            raise AssertionError("init: unknown type for variable %s" % var)

    body += indent(transferToC(info))

    c_process_str = c_process_template % (info.name, body)
    res = init_body + procedures_body + c_process_str
    return res

def transferIndexInputToC(hp: hcsp.InputChannel, index: int) -> str:
    ch_name = hp.ch_name
    var_name = hp.var_name

    if var_name:
        return "channels[%d].channelNo = %s;\nchannels[%d].type = 0;\nchannels[%d].pos = &%s;" % \
            (index, str(ch_name), index, index, str(var_name))
    else:
        return "channels[%d].channelNo = %s;\nchannels[%d].type = 0;\nchannels[%d].pos = midDouble;" % \
            (index, str(ch_name), index, index)

def transferIndexOutputToC(hp: hcsp.OutputChannel, index: int) -> str:
    ch_name = hp.ch_name
    e = hp.expr

    if e is None:
        return "channels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = midDouble;" % \
            (index, str(ch_name), index, index)
    elif isinstance(e, expr.AVar):
        return "channels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = &%s;" % \
            (index, str(ch_name), index, index, str(e))
    else:
        if isinstance(e, expr.AConst):
            if isinstance(e.value, str):
                return "midString = strInit(%s);\nchannels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = midString;" % \
                    (e.value, index, str(ch_name), index, index)
        elif isinstance(e, expr.ListExpr):
            return "%schannels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = midList;" % \
                (transferToCExpr(e),  index, str(ch_name), index, index)
        else:
            return "midDouble = (double*) malloc(sizeof(double));\n*midDouble = %s;\nchannels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = midDouble;" % \
                (transferToCExpr(e), index, str(ch_name), index, index)

def transferIndexCommToC(hp: hcsp.HCSP, index: int) -> str:
    if isinstance(hp, hcsp.InputChannel):
        return transferIndexInputToC(hp, index)
    elif isinstance(hp, hcsp.OutputChannel):
        return transferIndexOutputToC(hp, index)
    else:
        raise NotImplementedError

def transferToC(info: hcsp.HCSPInfo) -> str:
    def outputVars() -> str:
        formats = []
        vars = []
        for output in info.outputs:
            formats.append("%s = %%.3f" % output.varname)
            if output.expr is None:
                vars.append(output.varname)
            else:
                vars.append("(double) " + transferToCExpr(output.expr))
        format = ", ".join(formats)
        var = ", ".join(vars)
        res =  "if ((int) (localTime[threadNumber] * 1000 + 0.5) % (int) (output_step_size * 1000 + 0.5) == 0) {\n"
        res += "    printf(\"%%.3f: %s\\n\", localTime[threadNumber], %s);\n" % (format, var)
        res += "}\n"
        return res

    def rec(hp: hcsp.HCSP) -> str:
        c_str = ""
        if isinstance(hp, hcsp.Var):
            c_str = "var_" + hp.name
        elif isinstance(hp, hcsp.Skip):
            c_str = ";"
        elif isinstance(hp, hcsp.Wait):
            c_str = "delay(threadNumber, %s);" % str(hp.delay)
        elif isinstance(hp, hcsp.Assign):       # type checking
            var_name = hp.var_name
            e = hp.expr
            vars = hp.get_vars()
            type = 0
            global gl_var_type

            if isinstance(var_name, str):
                var_name = expr.AVar(str(var_name))

            if isinstance(var_name, expr.Expr):
                var_name = var_name
            else:
                var_name = tuple(var_name)
                assert len(var_name) >= 2 and all(isinstance(name, (str, expr.Expr)) for name in var_name)
                var_name = [expr.AVar(n) if isinstance(n, str) else n for n in var_name]

            ce = transferToCExpr(e)
            if isinstance(var_name, expr.Expr):
                var_str = str(var_name)
                if isinstance(e, expr.ListExpr):
                    c_str = "%s%s = *midList;" % (ce, var_str)
                else:
                    if isinstance(e, expr.FunExpr) and e.fun_name in ("top", "bottom", "get", "get_max"):
                        if isinstance(gl_var_type[var_str], RealType):
                            c_str = "%s = *(double*)%s;" % (var_str, ce)
                        elif isinstance(gl_var_type[var_str], StringType):
                            c_str = "%s = *(String*)%s;" % (var_str, ce)
                        elif isinstance(gl_var_type[var_str], ListType):
                            c_str = "%s = *(List*)%s;" % (var_str, ce)
                        else:
                            raise AssertionError("Assign Error: unknown type for variable %s" % var_str)
                    else:
                        c_str = "%s = %s;" % (var_str, ce)
            else:
                return_str = ""
                for n in var_name:
                    var_str = str(n)
                    if isinstance(e, expr.ListExpr):
                        return_str = return_str + "%s%s = *midList;" % (ce, var_str)
                    else:
                        if isinstance(e, expr.FunExpr) and e.fun_name in ("top", "bottom", "get"):
                            if isinstance(gl_var_type[var_str], RealType):
                                return_str = return_str + "%s = *(double*)%s;" % (var_str, ce)
                            elif isinstance(gl_var_type[var_str], StringType):
                                return_str = return_str + "%s = *(String*)%s;" % (var_str, ce)
                            elif isinstance(gl_var_type[var_str], ListType):
                                return_str = return_str + "%s = *(List*)%s;" % (var_str, ce)
                            else:
                                raise AssertionError("Assign Error: unknown type for variable %s" % var_str)
                        else:
                            return_str = return_str + "%s = %s;" % (var_str, ce)
                c_str = return_str
        elif isinstance(hp, hcsp.RandomAssign):
            var_name = hp.var_name
            e = hp.expr

            if isinstance(var_name, str):
                var_name = expr.AVar(str(var_name))
            if isinstance(var_name, expr.Expr):
                var_name = var_name
            else:
                var_name = tuple(var_name)
                assert len(var_name) >= 2 and all(isinstance(name, (str, expr.Expr)) for name in var_name)
                var_name = [expr.AVar(n) if isinstance(n, str) else n for n in var_name]

            if isinstance(var_name, expr.Expr):
                var_str = str(var_name)
                c_str = "%s = randomDouble();\nwhile(!(%s)) {\n%s = randomDouble();\n}" % (var_str, e, var_str)
            else:
                return_str = ""
                for var_str in var_name:
                    return_str = return_str + "%s = randomDouble();\nwhile(!(%s)) {\n%s = randomDouble();\n}" % (var_str, e, var_str)
                c_str = return_str
        elif isinstance(hp, hcsp.Loop):
            if hp.constraint == expr.true_expr:
                c_str = "while (1) {\n%s\n}" % indent(rec(hp.hp))
            else:
                c_str = "while (%s) {\n%s\n}" % (hp.constraint, indent(rec(hp.hp)))
        elif isinstance(hp, hcsp.ITE):
            if_hps = hp.if_hps
            else_hp = hp.else_hp

            res = "if (%s) { %s " % (transferToCExpr(if_hps[0][0]), rec(if_hps[0][1]))
            for cond, hp in if_hps[1:]:
                res += "} else if (%s) { %s " % (transferToCExpr(cond), rec(hp))
            if else_hp is None:
                res += "}"
            else:
                res += "} else { %s }" % rec(else_hp)

            c_str = res
        elif isinstance(hp, hcsp.Sequence):
            c_str = "\n".join(rec(seq) for seq in hp.hps)
        elif isinstance(hp, hcsp.InputChannel):
            ch_name = hp.ch_name
            var_name = hp.var_name
            if var_name:
                c_str = "channel.channelNo = %s;\nchannel.type = 0;\nchannel.pos = &%s;\ninput(threadNumber, channel);" % \
                    (str(ch_name), str(var_name))
            else:
                c_str = "channel.channelNo = %s;\nchannel.type = 0;\nchannel.pos = midDouble;\ninput(threadNumber, channel);" % \
                    (str(ch_name))
        elif isinstance(hp, hcsp.OutputChannel):
            ch_name = hp.ch_name
            e = hp.expr

            if e is None:
                return "channel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = midDouble;\noutput(threadNumber, channel);" % \
                    (str(ch_name))
            elif isinstance(e, expr.AVar):
                return "channel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = &%s;\noutput(threadNumber, channel);" % \
                    (str(ch_name), transferToCExpr(e))
            else:
                if isinstance(e, expr.AConst):
                    if isinstance(e.value, str):
                        return "midString = strInit(\"%s\");\nchannel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = midString;\noutput(threadNumber, channel);" % \
                            (e.value, str(ch_name))
                elif isinstance(e, expr.ListExpr):
                    return "%schannel.channelNo = %s;\nchannelchannel..type = 1;\nchannel.pos = midList;\noutput(threadNumber, channel);" % \
                        (transferToCExpr(e), str(ch_name))
                else:
                    return "midDouble = (double*) malloc(sizeof(double));\n*midDouble = %s;\nchannel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = midDouble;\noutput(threadNumber, channel);" % \
                        (transferToCExpr(e), str(ch_name))
        elif isinstance(hp, hcsp.IChoice):
            c_str = "if (getIchoice()) {%s} else {%s}" % (str(hp.hp1), str(hp.hp2))
        elif isinstance(hp, hcsp.ODE):
            eqs = hp.eqs
            constraint = hp.constraint

            res = "h = step_size;\n"
            loop_cp = ""
            if info.outputs:
                loop_cp += outputVars()
            var_names = []
            exprs = []
            for var_name, e in eqs:
                var_names.append(var_name)
                exprs.append(e)
                loop_cp += "double %s_ori = %s;\n" % (var_name, var_name)
            for var_name, e in eqs:
                loop_cp += "double %s_dot1 = %s;\n" % (var_name, transferToCExpr(e))
            for var_name, e in eqs:
                loop_cp += "%s = %s_ori + %s_dot1 * h / 2;\n" % (var_name, var_name, var_name)
            for var_name, e in eqs:
                loop_cp += "double %s_dot2 = %s;\n" % (var_name, transferToCExpr(e))
            for var_name, e in eqs:
                loop_cp += "%s = %s_ori + %s_dot2 * h / 2;\n" % (var_name, var_name, var_name)
            for var_name, e in eqs:
                loop_cp += "double %s_dot3 = %s;\n" % (var_name, transferToCExpr(e))
            for var_name, e in eqs:
                loop_cp += "%s = %s_ori + %s_dot3 * h;\n" % (var_name, var_name, var_name)
            for var_name, e in eqs:
                loop_cp += "double %s_dot4 = %s;\n" % (var_name, transferToCExpr(e))
            for var_name, e in eqs:
                loop_cp += "%s = %s_ori + (%s_dot1 + 2 * %s_dot2 + 2 * %s_dot3 + %s_dot4) * h / 6;\n" % (var_name, var_name, var_name, var_name, var_name, var_name)
            loop_cp += "delay(threadNumber, h);\n"
            loop_cp += "if (!(%s)) {\n\tbreak;\n}" % constraint
            res += "while (1) {\n%s\n}" % indent(loop_cp)
            c_str = res
        elif isinstance(hp, hcsp.ODE_Comm):
            eqs = hp.eqs
            constraint = hp.constraint     
            comm_hps = []
            out_hps = []
            for i in range(0, len(hp.io_comms)):
                io_comm = hp.io_comms[i]
                comm_hps.append(transferIndexCommToC(io_comm[0], i))
                out_hps.append(rec(io_comm[1]))

            res = ""
            for comm_hp in comm_hps:
                res += "%s\n" % comm_hp
            res += "interruptInit(threadNumber, %d, channels);\n" % len(comm_hps)
            choice_str = ""
            for i in range(0, len(out_hps)):
                if i > 0:
                    choice_str += "else "
                choice_str += "if (midInt == %d) {\n%s\n}" % (i, indent(out_hps[i]))
            res += "h = step_size;\nis_comm = 0;\n"
            loop_cp = ""
            var_names = []
            exprs = []
            for var_name, e in eqs:
                var_names.append(var_name)
                exprs.append(e)
                loop_cp += "double %s_ori = %s;\n" % (var_name, var_name)
            for var_name, e in eqs:
                loop_cp += "double %s_dot1 = %s;\n" % (var_name, e)
            for var_name, e in eqs:
                loop_cp += "%s = %s_ori + %s_dot1 * h / 2;\n" % (var_name, var_name, var_name)
            for var_name, e in eqs:
                loop_cp += "double %s_dot2 = %s;\n" % (var_name, e)
            for var_name, e in eqs:
                loop_cp += "%s = %s_ori + %s_dot2 * h / 2;\n" % (var_name, var_name, var_name)
            for var_name, e in eqs:
                loop_cp += "double %s_dot3 = %s;\n" % (var_name, e)
            for var_name, e in eqs:
                loop_cp += "%s = %s_ori + %s_dot3 * h;\n" % (var_name, var_name, var_name)
            for var_name, e in eqs:
                loop_cp += "double %s_dot4 = %s;\n" % (var_name, e)
            for var_name, e in eqs:
                update = "%s = %s_ori + (%s_dot1 + 2 * %s_dot2 + 2 * %s_dot3 + %s_dot4) * h / 6;\n" % (var_name, var_name, var_name, var_name, var_name, var_name)
                loop_cp += update
            loop_cp += "if (!(%s)) {\n" % constraint
            loop_cp += "    interruptClear(threadNumber, %d, channels);\n" % len(comm_hps)
            loop_cp += "    break;\n"
            loop_cp += "}\n"
            loop_cp += "midInt = interruptPoll(threadNumber, h, %d, channels);\n" % len(comm_hps)
            loop_cp += "if (midInt >= 0) {\n"
            loop_cp += "    break;\n"
            loop_cp += "}"
            res += "while (1) {\n%s\n}\n" % indent(loop_cp)
            res += choice_str
            c_str = res
        elif isinstance(hp, hcsp.SelectComm):
            comm_hps = []
            out_hps = []
            for i in range(0, len(hp.io_comms)):
                io_comm = hp.io_comms[i]
                comm_hps.append(transferIndexCommToC(io_comm[0], i) + '\n')
                out_hps.append(rec(io_comm[1]))
            res = ""
            for comm_hp in comm_hps:
                res += "%s" % comm_hp 
            res += "midInt = externalChoice(threadNumber, %d, channels);\n" % len(comm_hps)
            for i in range(0, len(out_hps)):
                if i > 0:
                    res += " else "
                res += "if (midInt == %d) {\n%s\n}" % (i, indent(out_hps[i]))
            c_str = res
        
        return c_str

    return rec(info.hp)

header = \
"""
#include <math.h>
#include "%s.h"
#include "hcsp2c.h"
"""
header_header = \
"""
#ifndef %s_h
#define %s_h

#define step_size %s
#define output_step_size %s
"""

main_header = \
"""
int main() {
    const int threadNumber = %d;
    const int channelNumber = %d;
    void* (*threadFuns[threadNumber])(void*);
"""

main_init = \
"""
    init(threadNumber, channelNumber);
    maxTime = %f;
"""



main_footer = \
"""
    run(threadNumber, channelNumber, threadFuns);

    destroy(threadNumber, channelNumber);
    return 0;
}
"""


def convertHps(name: str, infos: List[HCSPInfo], step_size:float = 1e-7, output_step_size:float = 1e-1,
               real_time:bool = False, max_time:float = 5.0) -> tuple:
    """Main function for HCSP to C conversion."""
    ctx = inferTypes(infos)

    res = ""
    res += header % (name)
    count = 0
    head_res = header_header % (name, name, step_size, output_step_size)
    for channel in ctx.channelTypes.keys():
        head_res += "#define %s %d\n" % (channel, count)
        count += 1

    threads_res = []
    for info in infos:
        code = transferToCProcess(name, info, ctx)
        threads_res.append((info.name, code))
        head_res += "void* %s (void* arg);\n" % info.name

    res += main_header % (len(infos), count)
    head_res += "#endif"

    # Simulate in real-time
    if real_time:
        res += "\tSIMULATE_REAL_TIME = 1;\n"

    for i, info in enumerate(infos):
        res += "\tthreadFuns[%d] = &%s;\n" % (i, info.name)

    res += main_init % max_time

    for i, (name, type) in enumerate(ctx.channelTypes.items()):
        res += "\tchannelNames[%d] = \"%s\";\n" % (i, name)
        if isinstance(type, RealType):
            res += "\tchannelTypes[%d] = 1;\n" % i
        elif isinstance(type, StringType):
            res += "\tchannelTypes[%d] = 2;\n" % i
        elif isinstance(type, ListType):
            res += "\tchannelTypes[%d] = 3;\n" % i
    
    res += main_footer

    return (res, head_res, threads_res)
