"""transfer HCSP to C programs, return str"""

from collections import OrderedDict

from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp.expr import *
from ss2hcsp.matlab import function
from ss2hcsp.util.topsort import topological_sort
import re

class Channel:
    """Models a channel identifier. It is a string followed by a list
    of integer or variable arguments.

    The usual channel is modeled by a string without arguments. Further
    arguments can be given for parameterized channels. Parameters that
    are already decided are indicated by integers. Those that still need
    to be matched are indicated by variables.

    """
    def __init__(self, name, args=None, meta=None):
        assert isinstance(name, str)
        if args is None:
            args = tuple()

        # Each argument is either integer, (unevaluated) expression, or variable
        assert isinstance(args, tuple) and all(isinstance(arg, (AExpr, int, str)) for arg in args)

        self.name = name
        self.args = args
        self.meta = meta

    def __str__(self):
        def str_arg(arg):
            # if isinstance(arg, str):
            #     return repr(arg)
            if isinstance(arg, AConst) and isinstance(arg.value, str) and arg.value[0] != "\"":
                return "\"" + arg.value + "\""
            else:
                return str(arg)
        return self.name + ''.join('[' + str_arg(arg) + ']' for arg in self.args)
    
    def __repr__(self):
        if self.args:
            return "Channel(%s,%s)" % (self.name, ','.join(str(arg) for arg in self.args))
        else:
            return "Channel(%s)" % self.name

    def __hash__(self):
        return hash(("CHANNEL", self.name, self.args))

    def __eq__(self, other):
        return self.name == other.name and self.args == other.args

    def __le__(self, other):
        return (self.name, self.args) <= (other.name, other.args)

    def __lt__(self, other):
        return (self.name, self.args) < (other.name, other.args)

    def subst(self, inst):
        if self.name in inst:
            target = inst[self.name]
            assert isinstance(target, Channel)
            return Channel(target.name, tuple(arg if isinstance(arg, (int, str)) else arg.subst(inst)
                                              for arg in target.args + self.args))
        else:
            return Channel(self.name, tuple(arg if isinstance(arg, (int, str)) else arg.subst(inst)
                                            for arg in self.args))

def transferToCChannel(hp):
    assert isinstance(hp, hcsp.Channel)
    return Channel(hp.name, hp.args)

class C:
    def __init__(self):
        self.type = None

    def get_vars(self):
        return set()

    def get_funs(self):
        return set()

    def get_chs(self):
        return set()

    def priority(self):
        if self.type == "parallel":
            return 30
        elif self.type == "select_comm":
            return 50
        elif self.type == "sequence":
            return 70
        elif self.type == "ichoice":
            return 80
        elif self.type == "condition":
            return 90
        else:
            return 100

    def size(self):
        """Returns size of HCSP program."""
        if isinstance(self, (Var, Skip, Wait, Assign, Assert, Test, Log,
                             InputChannel, OutputChannel)):
            return 1
        elif isinstance(self, (Sequence, Parallel)):
            return 1 + sum([hp.size() for hp in self.hps])
        elif isinstance(self, (Loop, Condition, Recursion)):
            return 1 + self.hp.size()
        elif isinstance(self, ODE):
            return 1
        elif isinstance(self, (ODE_Comm, SelectComm)):
            return 1 + sum([1 + out_hp.size() for comm_hp, out_hp in self.io_comms])
        elif isinstance(self, ITE):
            return 1 + sum([1 + hp.size() for cond, hp in self.if_hps]) + self.else_hp.size()
        else:
            raise NotImplementedError

    def subst_comm(self, inst):
        def subst_io_comm(io_comm):
            return (io_comm[0].subst_comm(inst), io_comm[1].subst_comm(inst))

        def subst_if_hp(if_hp):
            return (if_hp[0].subst(inst), if_hp[1].subst_comm(inst))

        def subst_ode_eq(ode_eq):
            return (ode_eq[0], ode_eq[1].subst(inst))

        if self.type in ('var', 'skip'):
            return self
        elif self.type == 'wait':
            return Wait(self.delay.subst(inst))
        elif self.type == 'assign':
            return Assign(self.var_name, self.expr.subst(inst))
        # elif self.type == 'assert':
        #     return Assert(self.bexpr.subst(inst), [expr.subst(inst) for expr in self.msgs])
        # elif self.type == 'test':
        #     return Test(self.bexpr.subst(inst), [expr.subst(inst) for expr in self.msgs])
        # elif self.type == 'log':
        #     return Log(self.pattern.subst(inst), exprs=[expr.subst(inst) for expr in self.exprs])
        elif self.type == 'input_channel':
            return InputChannel(self.ch_name.subst(inst), self.var_name)
        elif self.type == 'output_channel':
            if self.expr is None:
                return OutputChannel(self.ch_name.subst(inst))
            else:
                return OutputChannel(self.ch_name.subst(inst), self.expr.subst(inst))
        elif self.type == 'sequence':
            return Sequence(*(hp.subst_comm(inst) for hp in self.hps))
        elif self.type == 'ode':
            return ODE([subst_ode_eq(eq) for eq in self.eqs],
                       self.constraint.subst(inst), out_hp=self.out_hp.subst_comm(inst))
        elif self.type == 'ode_comm':
            return ODE_Comm([subst_ode_eq(eq) for eq in self.eqs],
                            self.constraint.subst(inst),
                            [subst_io_comm(io_comm) for io_comm in self.io_comms])
        elif self.type == 'loop':
            return Loop(self.hp.subst_comm(inst), constraint=self.constraint)
        elif self.type == 'condition':
            return Condition(self.cond.subst(inst), self.hp.subst_comm(inst))
        elif self.type == 'select_comm':
            return SelectComm(*(subst_io_comm(io_comm) for io_comm in self.io_comms))
        # elif self.type == 'recursion':
        #     return Recursion(self.hp.subst_comm(inst), entry=self.entry)
        elif self.type == 'ite':
            return ITE([subst_if_hp(if_hp) for if_hp in self.if_hps], self.else_hp.subst_comm(inst))
        else:
            print(self.type)
            raise NotImplementedError

def get_comm_chs(hp):
    """Returns the list of communication channels for the given program.
    
    Result is a list of pairs (ch_name, '?'/'!').
    
    """
    assert isinstance(hp, C)
    collect = []

    def rec(_hp):
        if _hp.type == 'input_channel':
            collect.append((_hp.ch_name, '?'))
        elif _hp.type == 'output_channel':
            collect.append((_hp.ch_name, '!'))
        elif _hp.type == 'sequence':
            for arg in _hp.hps:
                rec(arg)
        elif _hp.type == 'ode':
            if _hp.out_hp:
                rec(_hp.out_hp)
        elif _hp.type in ('ode_comm', 'select_comm'):
            for comm_hp, out_hp in _hp.io_comms:
                rec(comm_hp)
                rec(out_hp)
        elif _hp.type in ('loop', 'condition', 'recursion'):
            rec(_hp.hp)
        elif _hp.type == 'ite':
            for _, sub_hp in _hp.if_hps:
                rec(sub_hp)
            rec(_hp.else_hp)
    
    rec(hp)
    return list(OrderedDict.fromkeys(collect))


class CInfo:
    """C process with extra information."""
    def __init__(self, name, cp, *, outputs=None, procedures=None):
        self.name = name
        self.cp = cp
        
        # List of output variables, None indicates output everything
        self.outputs = outputs

        # List of declared procedures
        if procedures is None:
            procedures = []
        self.procedures = procedures

    def __str__(self):
        body = ""
        for procedure in self.procedures:
            body += str(procedure) + '\n'
        vars = self.cp.get_vars()
        if len(vars) > 0:
            body += 'int midInt, is_comm = 0; Channel channel, channels[%d]; double h = step_size; double nullVar,' % len(self.cp.get_chs())
            body += ",".join(str(var) for var in vars) + ' = 0;'
        # channels = self.cp.get_chs()
        # if len(channels) > 0:
        #     res += 'Channel ' + ",".join(str(channel) for channel in channels) + ';'
        body += str(self.cp)

        res = "void* %s (void* arg) { int threadNumber = 0; threadNumber = (int)(*((int*)arg)); %s return NULL;}" % (self.name, body)
        return res

    def __repr__(self):
        return "CInfo(%s, %s)" % (self.name, str(self.cp))

    def __eq__(self, other):
        return self.name == other.name and self.cp == other.cp

    def get_chs(self):
        ch_set = set()
        ch_set.update(self.cp.get_chs())
        return ch_set

def subst_comm_all(hp, inst):
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
        hp = hp.subst_comm({var: inst[var]})
    return hp

def C_subst(hp, inst):
    """Substitution of program variables for their instantiations."""
    assert isinstance(hp, C)
    if isinstance(hp, Var):
        if hp.name in inst:
            return inst[hp.name]
        else:
            return hp
    elif isinstance(hp, (Skip, Wait, Assign, InputChannel, OutputChannel)): # Assert, Test, Log
        return hp
    elif isinstance(hp, (Loop, Condition)): # Recursion
        hp.hp = C_subst(hp.hp, inst)
        return hp
    elif isinstance(hp, Sequence):
        hps = [C_subst(sub_hp, inst) for sub_hp in hp.hps]
        return Sequence(*hps)
    elif isinstance(hp, ODE):
        hp.out_hp = C_subst(hp.out_hp, inst)
        return hp
    elif isinstance(hp, (ODE_Comm, SelectComm)):
        hp.io_comms = tuple((io_comm[0], C_subst(io_comm[1], inst)) for io_comm in hp.io_comms)
        return hp
    elif isinstance(hp, ITE):
        hp.if_hps = tuple((e[0], C_subst(e[1], inst)) for e in hp.if_hps)
        hp.else_hp = C_subst(hp.else_hp, inst)
        return hp
    else:
        print(hp)
        raise NotImplementedError

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


def transferToCProcess(name, hp, step_size = 1e-7, total_time = 0, is_partial = -1):
    c_process_str = ""
    global gl_var_type
    gl_var_type = {}
    body = ""
    procedures = []
    for procedure in procedures:
        body += str(procedure) + '\n'
    vars = hp.get_vars()
    if len(vars) > 0:
        body += 'int midInt, is_comm = 0;\nString* minString = nullptr;\nChannel channel, channels[%d]; double h = step_size;\ndouble nullVar,' % len(hp.get_chs())
        body += ",".join(str(var) for var in vars) + ' = 0;\n'
    # channels = self.cp.get_chs()
    # if len(channels) > 0:
    #     res += 'Channel ' + ",".join(str(channel) for channel in channels) + ';'
    body += transferToC(hp, step_size, total_time, is_partial)

    c_process_str = "void* %s (void* arg) {\n int threadNumber = 0;\nthreadNumber = (int)(*((int*)arg));\n %s return NULL;\n}\n" % (name, body)
    return c_process_str


def transferToC(hp, step_size = 1e-7, total_time = 0, is_partial = -1):
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
            c_str = "%s = %s; " % (var_str, expr)
        else:
            return_str = ""
            for n in var_name:
                var_str = str(n)
                return_str = return_str + "%s = %s; " % (var_str, expr)
            c_str = return_str
    elif isinstance(hp, hcsp.RandomAssign):
        var_name = hp.var_name
        expr = hp.expr

        if isinstance(var_name, str):
            var_name = AVar(str(var_name))
        if isinstance(var_name, Expr):
            var_name = var_name
        elif isinstance(var_name,function.DirectName):
            var_name=var_name
        else:
            var_name = tuple(var_name)
            assert len(var_name) >= 2 and all(isinstance(name, (str, Expr)) for name in var_name)
            var_name = [AVar(n) if isinstance(n, str) else n for n in var_name]

        if isinstance(var_name, Expr):
            var_str = str(var_name)
            c_str = "%s = randomDouble(); while(!(%s)) {%s = randomDouble();}" % (var_str, expr, var_str)
        elif isinstance(var_name,function.DirectName):
            var_str=str(var_name)
            c_str = "%s = randomDouble(); while(!(%s)) {%s = randomDouble();}" % (var_str, expr, var_str)
        else:
            return_str = ""
            for var_str in var_name:
                return_str = return_str + "%s = randomDouble(); while(!(%s)) {%s = randomDouble();}" % (var_str, expr, var_str)
            c_str = return_str
    elif isinstance(hp, hcsp.Loop):
        if hp.constraint == true_expr:
            c_str = "while(1){%s}" % transferToC(hp.hp, step_size, total_time)
        else:
            c_str = "while(%s){%s}" % (str(hp.constraint), transferToC(hp.hp, step_size, total_time))
    # elif isinstance(hp, hcsp.Recursion):
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
        c_str = " ".join(
            transferToC(seq, step_size, total_time) if seq.priority() > hp.priority() else "{" + transferToC(seq, step_size, total_time) + "}"
            for seq in seqs)
    elif isinstance(hp, hcsp.InputChannel):
        ch_name = hp.ch_name
        var_name = hp.var_name

        if is_partial >= 0:
            if var_name:
                c_str = "channels[%d].channelNo = %s; channels[%d].type = 0; channels[%d].pos = &%s; " % (is_partial, str(ch_name), is_partial, is_partial, str(var_name))
            else:
                c_str = "channels[%d].channelNo = %s; channels[%d].type = 0; channels[%d].pos = &nullVar; " % (is_partial, str(ch_name), is_partial, is_partial)
        else :
            if var_name:
                c_str = "channel.channelNo = %s; channel.type = 0; channel.pos = &%s; input(threadNumber, channel);" % (str(ch_name), str(var_name))
            else:
                c_str = "channel.channelNo = %s; channel.type = 0; channel.pos = &nullVar; input(threadNumber, channel);" % (str(ch_name))
    elif isinstance(hp, hcsp.OutputChannel):
        ch_name = hp.ch_name
        expr = hp.expr

        if is_partial >= 0:
            if expr:
                return "channels[%d].channelNo = %s; channels[%d].type = 1; channels[%d].pos = &%s; " % (is_partial, str(ch_name), is_partial, is_partial, str(expr))
            else:
                return "channels[%d].channelNo = %s; channels[%d].type = 1; channels[%d].pos = &nullVar; " % (is_partial, str(ch_name), is_partial, is_partial)
        else :
            if expr:
                return "channel.channelNo = %s; channel.type = 1; channel.pos = &%s; output(threadNumber, channel);" % (str(ch_name), str(expr))
            else:
                return "channel.channelNo = %s; channel.type = 1; channel.pos = &nullVar; output(threadNumber, channel);" % (str(ch_name))
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
            loop_cp += "double %s_ori = %s;" % (var_name, var_name)
            trace_back += "double %s = %s_ori;" % (var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot1 = %s;" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot1 * h / 2;" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot2 = %s;" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot2 * h / 2;" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot3 = %s;" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot3 * h;" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot4 = %s;" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + (%s_dot1 + 2 * %s_dot2 + 2 * %s_dot3 + %s_dot4) * h / 6;" % (var_name, var_name, var_name, var_name, var_name, var_name)
        loop_cp += "if (%s) {delay(h);} else if (h > min_step_size){%s h = h / 2;} else {%s delay(h); break;}" % (str(constraint), trace_back, transferToC(out_hp, step_size, total_time))
        res += "while(1){%s}" % loop_cp
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
            choice_str += "if (midInt == %d) {%s}" % (i, out_hps[i])
        res += "h = step_size; is_comm = 0;"
        loop_cp = ""
        trace_back = ""
        var_names = []
        exprs = []
        for var_name, expr in eqs:
            var_names.append(var_name)
            exprs.append(expr)
            loop_cp += "double %s_ori = %s;" % (var_name, var_name)
            trace_back += "double %s = %s_ori;" % (var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot1 = %s;" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot1 * h / 2;" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot2 = %s;" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot2 * h / 2;" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot3 = %s;" % (var_name, expr)
        for var_name, expr in eqs:
            loop_cp += "%s = %s_ori + %s_dot3 * h;" % (var_name, var_name, var_name)
        for var_name, expr in eqs:
            loop_cp += "double %s_dot4 = %s;" % (var_name, expr)
        for var_name, expr in eqs:
            update = "%s = %s_ori + (%s_dot1 + 2 * %s_dot2 + 2 * %s_dot3 + %s_dot4) * h / 6;" % (var_name, var_name, var_name, var_name, var_name, var_name)
            loop_cp += update
        loop_cp += "if (is_comm == 1) {midInt = timedExternalChoice2(threadNumber, %d, midInt, channels); break;} else if (%s) {clock_t start = clock(); midInt = timedExternalChoice1(threadNumber, %d, h, channels); if (midInt == -1) {midInt = timedExternalChoice2(threadNumber, %d, midInt, channels);} else {is_comm = 1; %s h = (double)(clock() - start) / (double)CLOCKS_PER_SEC;}} else if (h > min_step_size){%s h = h / 2;} else {delay(h); break;}" % (len(comm_hps), str(constraint), len(comm_hps), len(comm_hps), trace_back, trace_back)
        res += "while(1){%s}" % loop_cp
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
            res += "if (midInt == %d) {%s}" % (i, out_hps[i])
        c_str = res
    
    return c_str

