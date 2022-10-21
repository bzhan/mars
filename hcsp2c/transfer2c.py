"""transfer HCSP to C programs, return str"""

from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp.expr import *
from ss2hcsp.matlab import function


gl_var_type = {} # key: var_name, value:type,  0 -> undef, 1 -> double, 2 -> string, 3 -> list

def transferToCExpr(expr):
    assert isinstance(expr, Expr)
    c_str = str(expr)
    if isinstance(expr, RelExpr):
        if expr.op == "==":
            if isinstance(expr.expr1, AConst):
                mid = expr.expr1
                expr.expr1 = expr.expr2
                expr.expr2 = mid
            if isinstance(expr.expr2, AConst):
                if isinstance(expr.expr2.value, str):
                    c_str = "strEqual(%s, &strInit(%s))" % (expr.expr1, expr.expr2.value)
                elif isinstance(expr.expr2, AVar) and expr.expr2.name in gl_var_type and gl_var_type[expr.expr2.name] == 2:
                    c_str = "strEqual(%s, %s)" % (expr.expr1, expr.expr2)
    elif isinstance(expr, AConst):
        if isinstance(expr.value, str):
            c_str = "strInit(%s)" % expr.value
    elif isinstance(expr, ListExpr):
        c_str = str(expr)

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

def transferToCProcess(name: str, hp: hcsp.HCSP, step_size = 1e-7, total_time = 0, is_partial = -1):
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

    body += transferToC(hp, step_size, total_time, is_partial)

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
        expr = hp.expr
        vars = hp.get_vars()
        type = 0
        global gl_var_type

        for var in vars:
            if var in gl_var_type and gl_var_type[var] != 0:
                type = gl_var_type[var]
                break

        if type == 0:
            if isinstance(expr, AConst) and isinstance(expr.value, str):
                type = 2
            elif isinstance(expr, ListExpr):
                type = 3
            elif isinstance(expr, AVar) and gl_var_type[expr.name] != 0:
                type = gl_var_type[expr.name]
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
            var_name = AVar(str(var_name))

        if isinstance(var_name, Expr):
            var_name = var_name
        elif isinstance(var_name,function.DirectName):
            var_name = var_name
        else:
            var_name = tuple(var_name)
            assert len(var_name) >= 2 and all(isinstance(name, (str, Expr)) for name in var_name)
            var_name = [AVar(n) if isinstance(n, str) else n for n in var_name]

        expr = transferToCExpr(expr)
        if isinstance(var_name, Expr):
            var_str = str(var_name)
            c_str = "%s = %s;\n" % (var_str, expr)
        else:
            return_str = ""
            for n in var_name:
                var_str = str(n)
                return_str = return_str + "%s = %s;\n" % (var_str, expr)
            c_str = return_str
    elif isinstance(hp, hcsp.RandomAssign):
        var_name = hp.var_name
        expr = hp.expr

        if isinstance(var_name, str):
            var_name = AVar(str(var_name))
        if isinstance(var_name, Expr):
            var_name = var_name
        else:
            var_name = tuple(var_name)
            assert len(var_name) >= 2 and all(isinstance(name, (str, Expr)) for name in var_name)
            var_name = [AVar(n) if isinstance(n, str) else n for n in var_name]

        if isinstance(var_name, Expr):
            var_str = str(var_name)
            c_str = "%s = randomDouble();\nwhile(!(%s)) {\n%s = randomDouble();\n}\n" % (var_str, expr, var_str)
        else:
            return_str = ""
            for var_str in var_name:
                return_str = return_str + "%s = randomDouble();\nwhile(!(%s)) {\n%s = randomDouble();\n}\n" % (var_str, expr, var_str)
            c_str = return_str
    elif isinstance(hp, hcsp.Loop):
        if hp.constraint == true_expr:
            c_str = "while (1) {\n%s\n}" % transferToC(hp.hp, step_size, total_time)
        else:
            c_str = "while (%s) {\n%s\n}" % (str(hp.constraint), transferToC(hp.hp, step_size, total_time))
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
        seqs = hp.hps
        c_str = "\n".join(
            transferToC(seq, step_size, total_time) if seq.priority() > hp.priority() else "{" + transferToC(seq, step_size, total_time) + "}"
            for seq in seqs)
    elif isinstance(hp, hcsp.InputChannel):
        ch_name = hp.ch_name
        var_name = hp.var_name

        if is_partial >= 0:
            if var_name:
                c_str = "channels[%d].channelNo = %s;\nchannels[%d].type = 0;\nchannels[%d].pos = &%s;\n" % (is_partial, str(ch_name), is_partial, is_partial, str(var_name))
            else:
                c_str = "channels[%d].channelNo = %s;\nchannels[%d].type = 0;\nchannels[%d].pos = &nullVar;\n" % (is_partial, str(ch_name), is_partial, is_partial)
        else :
            if var_name:
                c_str = "channel.channelNo = %s;\nchannel.type = 0;\nchannel.pos = &%s;\ninput(threadNumber, channel);\n" % (str(ch_name), str(var_name))
            else:
                c_str = "channel.channelNo = %s;\nchannel.type = 0;\nchannel.pos = &nullVar;\ninput(threadNumber, channel);\n" % (str(ch_name))
    elif isinstance(hp, hcsp.OutputChannel):
        ch_name = hp.ch_name
        expr = hp.expr

        if is_partial >= 0:
            if expr:
                return "channels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = &%s;\n" % (is_partial, str(ch_name), is_partial, is_partial, str(expr))
            else:
                return "channels[%d].channelNo = %s;\nchannels[%d].type = 1;\nchannels[%d].pos = &nullVar;\n" % (is_partial, str(ch_name), is_partial, is_partial)
        else :
            if expr:
                return "channel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = &%s;\noutput(threadNumber, channel);\n" % (str(ch_name), str(expr))
            else:
                return "channel.channelNo = %s;\nchannel.type = 1;\nchannel.pos = &nullVar;\noutput(threadNumber, channel);\n" % (str(ch_name))
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
        for var_name, expr in eqs:
            var_names.append(var_name)
            exprs.append(expr)
            loop_cp += "double %s_ori = %s;\n" % (var_name, var_name)
            trace_back += "double %s = %s_ori;\n" % (var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot1 = %s;\n" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot1 * h / 2;\n" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot2 = %s;\n" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot2 * h / 2;\n" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot3 = %s;\n" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot3 * h;\n" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot4 = %s;\n" % (var_name, expr)
        for var_name, expr in eqs:
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
        for var_name, expr in eqs:
            var_names.append(var_name)
            exprs.append(expr)
            loop_cp += "double %s_ori = %s;\n" % (var_name, var_name)
            trace_back += "double %s = %s_ori;\n" % (var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot1 = %s;\n" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot1 * h / 2;\n" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot2 = %s;\n" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot2 * h / 2;\n" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot3 = %s;\n" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot3 * h;\n" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot4 = %s;\n" % (var_name, expr)
        for var_name, expr in eqs:
            update = "%s = %s_ori + (%s_dot1 + 2 * %s_dot2 + 2 * %s_dot3 + %s_dot4) * h / 6;\n" % (var_name, var_name, var_name, var_name, var_name, var_name)
            loop_cp += update
        loop_cp += """
        if (is_comm == 1) {
            midInt = timedExternalChoice2(threadNumber, %d, midInt, channels);
            break;
        } else if (%s) {
            clock_t start = clock();
            midInt = timedExternalChoice1(threadNumber, %d, h, channels);
            if (midInt == -1) {
                midInt = timedExternalChoice2(threadNumber, %d, midInt, channels);
            } else {
                is_comm = 1;
                %s
                h = (double)(clock() - start) / (double) CLOCKS_PER_SEC;
            }
        } else if (h > min_step_size){
            %s
            h = h / 2;
        } else {
            delay(h);
            break;
        }""" % (len(comm_hps), str(constraint), len(comm_hps), len(comm_hps), trace_back, trace_back)
        res += "while(1){\n%s\n}\n" % loop_cp
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

double step_size = 1e7;
double min_step_size = 1e10;
"""

main_header = \
"""
int main() {
    printf("The program starts.\\n");
    fflush(stdout);
    const int threadNumber = %d;
    const int channelNumber = %d;
    void* (*threadFuns[threadNumber])(void*);
"""

main_footer = \
"""
    init(threadNumber, channelNumber, threadFuns);
    printf(\"The program is completed.\\n\");
    fflush(stdout);
    destroy(threadNumber, channelNumber);
    return 0;
}
"""

def convertHps(hps) -> str:
    """Main function for HCSP to C conversion."""
    channels = set()
    threads = []
    for hp in hps:
        channels.update(hp.get_chs())

    res = ""
    res += header
    count = 0
    for channel in channels:
        res += "const int %s = %d;\n" % (channel, count)
        count += 1

    for i, hp in enumerate(hps):
        name = "P" + str(i+1)
        threads.append(name)
        code = transferToCProcess(name, hp)
        res += code

    res += main_header % (len(threads), count)
    count = 0
    for thread in threads:
        res += "\tthreadFuns[%d] = &%s;\n" % (count, thread)
        count += 1

    res += main_footer
    return res
