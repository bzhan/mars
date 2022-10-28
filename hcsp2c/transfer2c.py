"""transfer HCSP to C programs, return str"""

from decimal import Decimal
from fractions import Fraction

from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import expr


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


def inferExprType(e: expr.Expr, hp_name: str, ctx: TypeContext):
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
    else:
        raise NotImplementedError

def inferTypes(hps):
    """Infer type of channel and variables.
    
    Input is a list of (name, hp) pairs.

    """
    ctx = TypeContext()
    for name, hp in hps:
        ctx.varTypes[name] = dict()

    def infer(hp_name, hp):
        if isinstance(hp, hcsp.Assign):
            v = hp.var_name
            if isinstance(v, expr.AVar):
                if v.name in ctx.varTypes[hp_name]:
                    pass   # Already know type of v, skip type checking
                else:
                    typ = inferExprType(hp.expr, hp_name, ctx)
                    if isinstance(typ, UndefType):
                        raise AssertionError("inferTypes: unknown type for right side of assignment")
                    else:
                        ctx.varTypes[hp_name][v.name] = typ
            else:
                pass  # skip type inference for arrays and fields

        elif isinstance(hp, hcsp.InputChannel):
            ch = hp.ch_name
            if ch.name in ctx.channelTypes:
                pass  # Already know type of ch, skip type checking
            elif hp.var_name is None:
                ctx.channelTypes[ch.name] = NullType()
            else:
                v = hp.var_name
                if isinstance(v, expr.AVar):
                    if v.name in ctx.varTypes[hp_name]:
                        ctx.channelTypes[ch.name] = ctx.varTypes[hp_name][v.name]
                    else:
                        raise AssertionError("inferTypes: unknown type for input variable")
                else:
                    raise NotImplementedError
        
        elif isinstance(hp, hcsp.OutputChannel):
            ch = hp.ch_name
            if ch.name in ctx.channelTypes:
                pass  # Already know type of ch, skip type checking
            elif hp.expr is None:
                ctx.channelTypes[ch.name] = NullType()
            else:
                e = hp.expr
                typ = inferExprType(e, hp_name, ctx)
                if isinstance(typ, UndefType):
                    raise AssertionError("inferTypes: unknown type for output expression")
                else:
                    ctx.channelTypes[ch.name] = typ
        
        elif isinstance(hp, (hcsp.ODE_Comm, hcsp.SelectComm)):
            for io_comm, _ in hp.io_comms:
                infer(hp_name, io_comm)

        elif isinstance(hp, hcsp.Sequence):
            for sub_hp in hp.hps:
                infer(hp_name, sub_hp)

        elif isinstance(hp, hcsp.ITE):
            for _, if_hp in hp.if_hps:
                infer(hp_name, if_hp)
            if hp.else_hp is not None:
                infer(hp_name, hp.else_hp)

        elif isinstance(hp, hcsp.Loop):
            infer(hp_name, hp.hp)

        else:
            pass  # No need for type inference on other commands

    for name, hp in hps:
        infer(name, hp)

    return ctx


def transferToCExpr(e: expr.Expr) -> str:
    """Convert HCSP expression into C expression."""
    assert isinstance(e, expr.Expr)
    c_str = str(e)
    if isinstance(e, expr.RelExpr):
        if e.op == "==":
            if isinstance(e.expr1, expr.AConst):
                mid = e.expr1
                e.expr1 = e.expr2
                e.expr2 = mid
            if isinstance(e.expr2, expr.AConst):
                if isinstance(e.expr2.value, str):
                    c_str = "strEqual(%s, &strInit(%s))" % (e.expr1, e.expr2.value)
                elif isinstance(e.expr2, expr.AVar) and e.expr2.name in gl_var_type and isinstance(gl_var_type[e.expr2.name], StringType):
                    c_str = "strEqual(%s, %s)" % (e.expr1, e.expr2)
    elif isinstance(e, expr.AConst):
        if isinstance(e.value, str):
            c_str = "*strInit(\"%s\")" % e.value
    elif isinstance(e, expr.ListExpr):
        c_str = "midList = listInit();\n"
        for i in range(e.count):
            b = e.args[i]
            if isinstance(b, expr.AVar):
                if isinstance(gl_var_type[b.name], RealType):
                    c_str += "midList = listPush(midList, (void*)(&%s), 1)" % b
                elif isinstance(gl_var_type[b.name], StringType):
                    c_str += "midList = listPush(midList, (void*)(&%s), 2)" % b
                elif isinstance(gl_var_type[b.name], ListType):
                    c_str += "midList = listPush(midList, (void*)(&%s), 3)" % b
            elif isinstance(b, expr.AConst) and isinstance(b.value, str):
                c_str += "midList = listPush(midList, (void*)strInit(%s), 2)" % b
            elif isinstance(b, expr.ListExpr):
                raise AssertionError("cannot push a raw list to a list")
            else:
                c_str += "midList = listPushNum(midList, %s)" % b

    elif isinstance(e, expr.FunExpr):
        args = e.exprs
        # Special functions
        if e.fun_name == "min":
            return "min(%d, *args)" % len(args)
        elif e.fun_name == "max":
            return "max(%d, *args)" % len(args)
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
                return "*listPushNum(&%s, %s)" % (a, b)

        #     if not isinstance(a, list):
        #         a = [a]
        #     if not isinstance(b, list):
        #         b = [b]
        #     return a + b
        elif e.fun_name == "pop":
            a, = args
            return "*listPop(&%s)" % a
        elif e.fun_name == "top":
            a, = args
            return "listTop(&%s)" % a
        elif e.fun_name == "bottom":
            a, = args
            return "listBottom(&%s)" % a
        # elif e.fun_name == "get":
        #     a, = args
        #     assert isinstance(a, list)
        #     if len(a) == 0:
        #         raise SimulatorException('When evaluating %s: argument is empty' % expr)
        #     return a[1:]


    return c_str


c_process_template = \
"""
void* %s (void* arg) {
    int threadNumber = 0;
    threadNumber = (int)(*((int*)arg));
    %s
    threadState[threadNumber] = STATE_STOPPED;
    updateCurrentTime(threadNumber);
    return NULL;
}"""

body_template = \
"""
    int midInt = 0;
    int is_comm = 0;
    String* midString = NULL;
    List* midList = NULL;
    Channel channel;
    Channel channels[%d];
    double h = step_size;
    double* midDouble = NULL;
"""

def transferToCProcess(name: str, hp: hcsp.HCSP, context: TypeContext, total_time = 0, is_partial = -1):
    """Convert HCSP process with given name to a C function"""
    c_process_str = ""
    global gl_var_type
    gl_var_type = context.varTypes[name]
    body = ""
    procedures = []
    for procedure in procedures:
        body += str(procedure) + '\n'
    vars = hp.get_vars()
    body += body_template % len(hp.get_chs())
    for var in vars:
        if isinstance(context.varTypes[name][var], RealType):
            body += "\tdouble %s = 0.0;\n" % var
        elif isinstance(context.varTypes[name][var], StringType):
            body += "\tString %s;\n" % var
        elif isinstance(context.varTypes[name][var], ListType):
            body += "\tList %s;\n" % var
        else:
            raise AssertionError("init: unknown type for variable %s" % var)

    body += indent(transferToC(hp, total_time, is_partial))

    c_process_str = c_process_template % (name, body)
    return c_process_str


def transferToC(hp: hcsp.HCSP, total_time = 0, is_partial = -1):
    assert isinstance(hp, hcsp.HCSP)

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
                if isinstance(e, expr.FunExpr) and e.fun_name in ("top", "bottom", "get"):
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
            c_str = "while (1) {\n%s\n}" % indent(transferToC(hp.hp, total_time))
        else:
            c_str = "while (%s) {\n%s\n}" % (hp.constraint, indent(transferToC(hp.hp, total_time)))
    elif isinstance(hp, hcsp.ITE):
        if_hps = hp.if_hps
        else_hp = hp.else_hp

        res = "if (%s) { %s " % (if_hps[0][0], transferToC(if_hps[0][1], total_time))
        for cond, hp in if_hps[1:]:
            res += "} else if (%s) { %s " % (cond, transferToC(hp, total_time))
        if else_hp is None:
            res += "}"
        else:
            res += "} else { %s }" % transferToC(else_hp, total_time)

        c_str = res
    elif isinstance(hp, hcsp.Sequence):
        c_str = "\n".join(transferToC(seq, total_time) for seq in hp.hps)
    elif isinstance(hp, hcsp.InputChannel):
        ch_name = hp.ch_name
        var_name = hp.var_name

        if is_partial >= 0:
            if var_name:
                c_str = "channels[%d].channelNo = %s;\nchannels[%d].type = 0;\nchannels[%d].pos = &%s;" % (is_partial, str(ch_name), is_partial, is_partial, str(var_name))
            else:
                c_str = "channels[%d].channelNo = %s;\nchannels[%d].type = 0;\nchannels[%d].pos = midDouble;" % (is_partial, str(ch_name), is_partial, is_partial)
        else :
            if var_name:
                c_str = "channel.channelNo = %s;\nchannel.type = 0;\nchannel.pos = &%s;\ninput(threadNumber, channel);" % (str(ch_name), str(var_name))
            else:
                c_str = "channel.channelNo = %s;\nchannel.type = 0;\nchannel.pos = midDouble;\ninput(threadNumber, channel);" % (str(ch_name))
    elif isinstance(hp, hcsp.OutputChannel):
        ch_name = hp.ch_name
        e = hp.expr

        if is_partial >= 0:
            if e is None:
                return "channels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = midDouble;" % (is_partial, str(ch_name), is_partial, is_partial)
            elif isinstance(e, expr.AVar):
                return "channels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = &%s;" % (is_partial, str(ch_name), is_partial, is_partial, str(e))
            else:
                if isinstance(e, expr.AConst):
                    if isinstance(e.value, str):
                        return "midString = strInit(\"%s\");\nchannels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = midString;" % (e.value, is_partial, str(ch_name), is_partial, is_partial)
                elif isinstance(e, expr.ListExpr):
                    return "%schannels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = midList;" % (transferToCExpr(e),  is_partial, str(ch_name), is_partial, is_partial)
                else:
                    return "midDouble = (double*) malloc(sizeof(double));\n*midDouble = %s;\nchannels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = midDouble;" % (transferToCExpr(e), is_partial, str(ch_name), is_partial, is_partial)
        else:
            if e is None:
                return "channel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = midDouble;\noutput(threadNumber, channel);" % (str(ch_name))
            elif isinstance(e, expr.AVar):
                return "channel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = &%s;\noutput(threadNumber, channel);" % (str(ch_name), str(e))
            else:
                if isinstance(e, expr.AConst):
                    if isinstance(e.value, str):
                        return "midString = strInit(\"%s\");\nchannel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = midString;\noutput(threadNumber, channel);" % (e.value, str(ch_name))
                elif isinstance(e, expr.ListExpr):
                    return "%schannel.channelNo = %s;\nchannelchannel..type = 1;\nchannel.pos = midList;\noutput(threadNumber, channel);" % (transferToCExpr(e), str(ch_name))
                else:
                    return "midDouble = (double*) malloc(sizeof(double));\n*midDouble = %s;\nchannel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = midDouble;\noutput(threadNumber, channel);" % (transferToCExpr(e), str(ch_name))
    elif isinstance(hp, hcsp.IChoice):
        c_str = "if (getIchoice()) {%s} else {%s}" % (str(hp.hp1), str(hp.hp2))
    elif isinstance(hp, hcsp.ODE):
        eqs = hp.eqs
        constraint = hp.constraint

        res = "h = step_size;\n"
        loop_cp = ""
        trace_back = ""
        var_names = []
        exprs = []
        for var_name, e in eqs:
            var_names.append(var_name)
            exprs.append(e)
            loop_cp += "double %s_ori = %s;\n" % (var_name, var_name)
            trace_back += "double %s = %s_ori;\n" % (var_name, var_name)
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
            comm_hps.append(transferToC(io_comm[0], total_time, i))
            out_hps.append(transferToC(io_comm[1], total_time))

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
        trace_back = ""
        var_names = []
        exprs = []
        for var_name, e in eqs:
            var_names.append(var_name)
            exprs.append(e)
            loop_cp += "double %s_ori = %s;\n" % (var_name, var_name)
            trace_back += "double %s = %s_ori;\n" % (var_name, var_name)
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
            comm_hps.append(transferToC(io_comm[0], total_time, i) + '\n')
            out_hps.append(transferToC(io_comm[1], total_time))
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


header = \
"""
#include "hcsp2c.h"

double step_size = %s;
double min_step_size = 1e-10;
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



def convertHps(hps, step_size:float = 1e-7, real_time:bool = False, maxTime:float = 5.0) -> str:
    """Main function for HCSP to C conversion."""
    ctx = inferTypes(hps)

    res = ""
    res += header % step_size
    count = 0
    for channel in ctx.channelTypes.keys():
        res += "const int %s = %d;\n" % (channel, count)
        count += 1

    for name, hp in hps:
        code = transferToCProcess(name, hp, ctx)
        res += code

    res += main_header % (len(hps), count)

    # Simulate in real-time
    if real_time:
        res += "\tSIMULATE_REAL_TIME = 1;\n"

    for i, (name, _) in enumerate(hps):
        res += "\tthreadFuns[%d] = &%s;\n" % (i, name)

    res += main_init % maxTime

    for i, (name, type) in enumerate(ctx.channelTypes.items()):
        res += "\tchannelNames[%d] = \"%s\";\n" % (i, name)
        if isinstance(type, RealType):
            res += "\tchannelTypes[%d] = 1;\n" % i
        elif isinstance(type, StringType):
            res += "\tchannelTypes[%d] = 2;\n" % i
        elif isinstance(type, ListType):
            res += "\tchannelTypes[%d] = 3;\n" % i
    
    res += main_footer

    return res
