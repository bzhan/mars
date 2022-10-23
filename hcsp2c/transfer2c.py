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
                elif isinstance(e.expr2, expr.AVar) and e.expr2.name in gl_var_type and gl_var_type[e.expr2.name] == 2:
                    c_str = "strEqual(%s, %s)" % (e.expr1, e.expr2)
    elif isinstance(e, expr.AConst):
        if isinstance(e.value, str):
            c_str = "strInit(%s)" % e.value
    elif isinstance(e, expr.ListExpr):
        c_str = str(e)

    return c_str


c_process_template = \
"""
void* %s (void* arg) {
    int threadNumber = 0;
    threadNumber = (int)(*((int*)arg));
    %s
    return NULL;
}"""

body_template = \
"""
    int midInt = 0;
    int is_comm = 0;
    String* minString = NULL;
    Channel channel;
    Channel channels[%d];
    double h = step_size;
    double nullVar = 0.0;
"""

interrupt_template = \
"""
if (is_comm == 1) {{
    midInt = timedExternalChoice2(threadNumber, {numChannel}, midInt, channels);
    break;
}} else if ({constraint}) {{
    clock_t start = clock();
    midInt = timedExternalChoice1(threadNumber, {numChannel}, h, channels);
    if (midInt == -1) {{
        midInt = timedExternalChoice2(threadNumber, {numChannel}, midInt, channels);
    }} else {{
        is_comm = 1;
        {traceBack}
        h = (double)(clock() - start) / (double) CLOCKS_PER_SEC;
    }}
}} else if (h > min_step_size) {{
    {traceBack}
    h = h / 2;
}} else {{
    delay(h);
    break;
}}
"""

def transferToCProcess(name: str, hp: hcsp.HCSP, step_size = 1e-7, total_time = 0, is_partial = -1):
    """Convert HCSP process with given name to a C function"""
    c_process_str = ""
    global gl_var_type
    gl_var_type = {}
    body = ""
    procedures = []
    for procedure in procedures:
        body += str(procedure) + '\n'
    vars = hp.get_vars()

    body += body_template % len(hp.get_chs())
    for var in vars:
        body += "\tdouble %s = 0.0;\n" % var

    body += indent(transferToC(hp, step_size, total_time, is_partial))

    c_process_str = c_process_template % (name, body)
    return c_process_str


def transferToC(hp: hcsp.HCSP, step_size: float = 1e-7, total_time = 0, is_partial = -1):
    assert isinstance(hp, hcsp.HCSP)

    c_str = ""
    if isinstance(hp, hcsp.Var):
        c_str = "var_" + hp.name
    elif isinstance(hp, hcsp.Skip):
        c_str = ";"
    elif isinstance(hp, hcsp.Wait):
        c_str = "delay(%s);" % str(hp.delay)
    elif isinstance(hp, hcsp.Assign):       # type checking
        var_name = hp.var_name
        e = hp.expr
        vars = hp.get_vars()
        type = 0
        global gl_var_type

        for var in vars:
            if var in gl_var_type and gl_var_type[var] != 0:
                type = gl_var_type[var]
                break

        if type == 0:
            if isinstance(e, expr.AConst) and isinstance(e.value, str):
                type = 2
            elif isinstance(e, expr.ListExpr):
                type = 3
            elif isinstance(e, expr.AVar) and gl_var_type[e.name] != 0:
                type = gl_var_type[e.name]
            else:
                type = 1

        for var in vars:
            if var in gl_var_type:
                if gl_var_type[var] == 0:
                    gl_var_type[var] = type
                else:
                    assert gl_var_type[var] == type
            else:
                gl_var_type[var] = type

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
            c_str = "%s = %s;" % (var_str, ce)
        else:
            return_str = ""
            for n in var_name:
                var_str = str(n)
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
            c_str = "while (1) {\n%s\n}" % indent(transferToC(hp.hp, step_size, total_time))
        else:
            c_str = "while (%s) {\n%s\n}" % (hp.constraint, indent(transferToC(hp.hp, step_size, total_time)))
    elif isinstance(hp, hcsp.ITE):
        if_hps = hp.if_hps
        else_hp = hp.else_hp

        res = "if (%s) { %s " % (if_hps[0][0], transferToC(if_hps[0][1], step_size, total_time))
        for cond, hp in if_hps[1:]:
            res += "} else if (%s) { %s " % (cond, transferToC(hp, step_size, total_time))
        if else_hp is None:
            res += "}"
        else:
            res += "} else { %s }" % transferToC(else_hp, step_size, total_time)

        c_str = res
    elif isinstance(hp, hcsp.Sequence):
        c_str = "\n".join(transferToC(seq, step_size, total_time) for seq in hp.hps)
    elif isinstance(hp, hcsp.InputChannel):
        ch_name = hp.ch_name
        var_name = hp.var_name

        if is_partial >= 0:
            if var_name:
                c_str = "channels[%d].channelNo = %s;\nchannels[%d].type = 0;\nchannels[%d].pos = &%s;" % (is_partial, str(ch_name), is_partial, is_partial, str(var_name))
            else:
                c_str = "channels[%d].channelNo = %s;\nchannels[%d].type = 0;\nchannels[%d].pos = &nullVar;" % (is_partial, str(ch_name), is_partial, is_partial)
        else :
            if var_name:
                c_str = "channel.channelNo = %s;\nchannel.type = 0;\nchannel.pos = &%s;\ninput(threadNumber, channel);" % (str(ch_name), str(var_name))
            else:
                c_str = "channel.channelNo = %s;\nchannel.type = 0;\nchannel.pos = &nullVar;\ninput(threadNumber, channel);" % (str(ch_name))
    elif isinstance(hp, hcsp.OutputChannel):
        ch_name = hp.ch_name
        e = hp.expr

        if is_partial >= 0:
            if e is not None:
                return "channels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = &%s;" % (is_partial, str(ch_name), is_partial, is_partial, str(e))
            else:
                return "channels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = &nullVar;" % (is_partial, str(ch_name), is_partial, is_partial)
        else:
            if e is not None:
                return "channel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = &%s;\noutput(threadNumber, channel);" % (str(ch_name), str(e))
            else:
                return "channel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = &nullVar;\noutput(threadNumber, channel);" % (str(ch_name))
    elif isinstance(hp, hcsp.IChoice):
        c_str = "if (getIchoice()) {%s} else {%s}" % (str(hp.hp1), str(hp.hp2))
    elif isinstance(hp, hcsp.ODE):
        eqs = hp.eqs
        constraint = hp.constraint
        out_hp = hp.out_hp

        res = "h = %f;" % step_size
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
        loop_cp += \
        """
        if (%s) {
            delay(h);
        } else if (h > min_step_size) {
            %s
            h = h / 2;
        } else {
            %s
            delay(h);
            break;
        }
        """ % (str(constraint), trace_back, transferToC(out_hp, step_size, total_time))
        res += "while(1){\n%s\n}" % loop_cp
        c_str = res
    elif isinstance(hp, hcsp.ODE_Comm):
        eqs = hp.eqs
        constraint = hp.constraint     
        comm_hps = []
        out_hps = []
        for i in range(0, len(hp.io_comms)):
            io_comm = hp.io_comms[i]
            comm_hps.append(transferToC(io_comm[0], step_size, total_time, i))
            out_hps.append(transferToC(io_comm[1], step_size, total_time))

        res = ""
        for comm_hp in comm_hps:
            res += "%s" % comm_hp
        choice_str = ""
        for i in range(0, len(out_hps)):
            if i > 0:
                choice_str += "else "
            choice_str += "if (midInt == %d) {\n%s\n}" % (i, out_hps[i])
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
        loop_cp += interrupt_template.format(numChannel=len(comm_hps), constraint=str(constraint),
                                             traceBack=trace_back)
        res += "while (1) {\n%s\n}\n" % loop_cp
        res += choice_str
        c_str = res
    elif isinstance(hp, hcsp.SelectComm):
        comm_hps = []
        out_hps = []
        for i in range(0, len(hp.io_comms)):
            io_comm = hp.io_comms[i]
            comm_hps.append(transferToC(io_comm[0], step_size, total_time, i))
            out_hps.append(transferToC(io_comm[1], step_size, total_time))
        res = ""
        for comm_hp in comm_hps:
            res += "%s" % comm_hp 
        res += "midInt = externalChoice(threadNumber, %d, channels);" % len(comm_hps)
        for i in range(0, len(out_hps)):
            if i > 0:
                res += "else "
            res += "if (midInt == %d) {\n%s\n}" % (i, out_hps[i])
        c_str = res
    
    return c_str


header = \
"""
#include "hcsp2c.h"

double step_size = 1e-7;
double min_step_size = 1e-10;
"""

main_header = \
"""
int main() {
    const int threadNumber = %d;
    const int channelNumber = %d;
    void* (*threadFuns[threadNumber])(void*);
"""

main_footer = \
"""
    init(threadNumber, channelNumber);
    maxTime = 5.0;

    channelNames[0] = "p2c";
    channelNames[1] = "c2p";
    run(threadNumber, threadFuns);

    destroy(threadNumber, channelNumber);
    return 0;
}
"""

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


def convertHps(hps) -> str:
    """Main function for HCSP to C conversion."""
    ctx = inferTypes(hps)

    res = ""
    res += header
    count = 0
    for channel in ctx.channelTypes.keys():
        res += "const int %s = %d;\n" % (channel, count)
        count += 1

    for name, hp in hps:
        code = transferToCProcess(name, hp)
        res += code

    res += main_header % (len(hps), count)
    for i, (name, _) in enumerate(hps):
        res += "\tthreadFuns[%d] = &%s;\n" % (i, name)

    res += main_footer
    return res
