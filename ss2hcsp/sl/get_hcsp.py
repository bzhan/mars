from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.sl.system import System
from ss2hcsp.sl.sl_line import SL_Line
# from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.expr import *
# from ss2hcsp.hcsp.parser import aexpr_parser, bexpr_parser

# from functools import reduce
from ss2hcsp.sl.sl_diagram import get_gcd
# from math import gcd
import operator
from itertools import product


def translate_continuous(diag):
    """Translate the given diagram to an HCSP program."""

    """Some stateless blocks, such as add and gain, are treated as
    continuous here, so we have to delete these blocks and subsititue
    the corresponding variables."""
    blocks = diag["diag"]
    # Get non-continuous blocks from blocks_dict
    non_con_blocks = {block.name: block for block in blocks if block.type not in ["integrator"]}
    cond_inst = Conditional_Inst()  # an object for variable substitution
    while non_con_blocks:
        delete_block = []
        for block in non_con_blocks.values():
            src_set = set()
            for dest_line in block.dest_lines:
                src_set.add(dest_line.src)
            if src_set.isdisjoint(set(non_con_blocks.keys())):
                in_vars = [line.name for line in block.dest_lines]
                out_var = block.src_lines[0][0].name  # Assumed that there is only one output of each block
                res_expr = None
                if block.type == "constant":
                    assert in_vars == []
                    cond_inst.add(var_name=out_var, cond_inst=[(BConst(True), AConst(block.value))])
                elif block.type in ["gain", "bias", "abs", "not"]:  # One input, one output
                    in_var = in_vars[0]
                    if block.type == "gain":
                        res_expr = TimesExpr(signs="**", exprs=[AVar(in_var), AConst(block.factor)])
                    elif block.type == "bias":
                        res_expr = PlusExpr(signs="++", exprs=[AVar(in_var), AConst(block.bias)])
                    elif block.type == "abs":
                        res_expr = FunExpr(fun_name="abs", exprs=[AVar(in_var)])
                    elif block.type == "not":
                        res_expr = PlusExpr(signs="+-", exprs=[AConst(1), AVar(in_var)])
                    cond_inst.add(var_name=out_var, cond_inst=[(BConst(True), res_expr)])
                elif block.type in ["add", "divide"]:  # Multiple inputs, one output
                    assert len(in_vars) == len(block.dest_spec)
                    exprs = [AVar(var) for var in in_vars]
                    if block.type == "add":
                        res_expr = PlusExpr(signs=block.dest_spec, exprs=exprs)
                    elif block.type == "divide":
                        res_expr = TimesExpr(signs=block.dest_spec, exprs=exprs)
                    cond_inst.add(var_name=out_var, cond_inst=[(BConst(True), res_expr)])
                elif block.type in ["or", "and", "min_max"]:
                    assert len(in_vars) == block.num_dest
                    exprs = [AVar(var) for var in in_vars]
                    if block.type == "or":
                        res_expr = FunExpr(fun_name="max", exprs=exprs)
                    elif block.type == "and":
                        res_expr = FunExpr(fun_name="min", exprs=exprs)
                    elif block.type == "min_max":
                        res_expr = FunExpr(fun_name=block.fun_name, exprs=exprs)
                    cond_inst.add(var_name=out_var, cond_inst=[(BConst(True), res_expr)])
                elif block.type == "relation":
                    cond0 = RelExpr(op=block.relation, expr1=AVar(in_vars[0]), expr2=AVar(in_vars[1]))
                    cond1 = cond0.neg()
                    cond_inst.add(var_name=out_var, cond_inst=[(cond0, AConst(1)), (cond1, AConst(0))])
                elif block.type == "switch":
                    cond0 = RelExpr(op=block.relation, expr1=AVar(in_vars[1]), expr2=AConst(block.threshold))
                    cond2 = cond0.neg()
                    cond_inst.add(var_name=out_var, cond_inst=[(cond0, AVar(in_vars[0])), (cond2, AVar(in_vars[2]))])
                elif block.type == "saturation":
                    in_var = in_vars[0]
                    cond0 = RelExpr(op=">", expr1=AVar(in_var), expr2=AConst(block.up_lim))
                    cond1 = RelExpr(op="<", expr1=AVar(in_var), expr2=AConst(block.low_lim))
                    cond2 = LogicExpr(op="&&", expr1=cond0.neg(), expr2=cond1.neg())
                    cond_inst.add(var_name=out_var, cond_inst=[(cond0, AConst(block.up_lim)),
                                                               (cond1, AConst(block.low_lim)),
                                                               (cond2, AVar(in_var))])
                elif block.type == "unit_delay":
                    in_var = in_vars[0]
                    assert isinstance(block.delay, AExpr)
                    cond0 = RelExpr(op="<=", expr1=AVar("t"), expr2=block.delay)
                    cond1 = RelExpr(op=">", expr1=AVar("t"), expr2=block.delay)
                    cond_inst.add(var_name=out_var,
                                  cond_inst=[(cond0, AConst(block.init_value)),
                                             (cond1, FunExpr(fun_name="delay",
                                                             exprs=[AVar(in_var), block.delay]))])
                delete_block.append(block.name)
        assert delete_block
        for name in delete_block:
            del non_con_blocks[name]

    """Get differential equations"""
    # Initial values for variables
    init_hps = []
    ode_eqs = []
    for block in blocks:
        if block.type == "integrator":
            src_name = block.src_lines[0][0].name
            init_hps.append(hp.Assign(var_name=src_name, expr=AConst(block.init_value)))
            dest_name = block.dest_lines[0].name
            ode_eqs.append((src_name, AVar(dest_name)))
        elif block.type == "unit_delay":
            src_name = block.src_lines[0][0].name
            init_hps.append(hp.Assign(var_name=src_name, expr=AConst(block.init_value)))
            ode_eqs.append((src_name, AConst(0)))

    # init_hps.append(hp.Assign(var_name="t", expr=AConst(0)))
    # ode_eqs.append(("t", AConst(1)))

    # Add communication for each port
    in_channels = diag["in"]
    out_channels = diag["out"]

    # Delete useless variables in cond_inst.data
    in_var_ode = set(in_var.name for _, in_var in ode_eqs if hasattr(in_var, "name"))  # isinstance(in_var, AVar)
    delete_vars = [var for var in cond_inst.data.keys() if var not in in_var_ode.union(set(ch for ch, _ in out_channels))]
    for var in delete_vars:
        del cond_inst.data[var]

    """Substitute variables in the ODEs by cond_inst.data"""
    # var_cond_exprs = [(var, cond_exprs) for var, cond_exprs in var_dict.items()]
    var_cond_exprs = [(var, cond_exprs) for var, cond_exprs in cond_inst.data.items()]
    var_list = [e[0] for e in var_cond_exprs]  # e[0] is a variable name
    cond_exprs_list = [e[1] for e in var_cond_exprs]  # e[1] is the list of (condition, expression) pairs wrt. e[0]
    if len(var_list) == 0:  # Do not need to substitute
        in_channel_hps = [(hp.InputChannel(ch_name="ch_" + var_name + bran_num, var_name=var_name), hp.Skip())
                          for var_name, bran_num in sorted(in_channels)]
        out_channel_hps = [(hp.OutputChannel(ch_name="ch_" + var_name + bran_num, expr=AVar(var_name)), hp.Skip())
                           for var_name, bran_num in sorted(out_channels)]
        comm_hps = in_channel_hps + out_channel_hps
        ode_hp = hp.ODE_Comm(eqs=ode_eqs, constraint=BConst(True), io_comms=comm_hps)
        return hp.Sequence(hp.Sequence(*init_hps), hp.Loop(ode_hp))
    else:  # len(var_list) >= 2
        compositions = product(*cond_exprs_list)
    ode_hps = []
    for composition in compositions:
        new_ode_eqs = []
        constraints = set()
        # constraints.add("True")
        comm_hps = [(hp.InputChannel(ch_name="ch_" + var_name + bran_num, var_name=var_name), hp.Skip())
                    for var_name, bran_num in sorted(in_channels)]
        for out_var, in_var in ode_eqs:  # isinstance(out_var, str) and isinstance(in_var, AVar)
            if hasattr(in_var, "name") and in_var.name in var_list:
                cond = composition[var_list.index(in_var.name)][0]
                _expr = composition[var_list.index(in_var.name)][1]
                # new_ode_eqs.append((out_var, aexpr_parse(expr)))
                new_ode_eqs.append((out_var, _expr))
                if cond != BConst(True):
                    constraints.add(cond)
            else:
                new_ode_eqs.append((out_var, in_var))
        # print("new_ode_eqs = ", new_ode_eqs)
        for out_channel, bran_num in sorted(out_channels):
            # print("ch_" + out_channel + "!")
            if out_channel in var_list:
                cond = composition[var_list.index(out_channel)][0]
                _expr = composition[var_list.index(out_channel)][1]
                comm_hps.append(
                    (hp.OutputChannel(ch_name="ch_" + out_channel + bran_num, expr=_expr), hp.Skip()))
                # comm_hps.append((hp.OutputChannel(var_name=out_channel, expr=aexpr_parse(expr)), hp.Skip()))
                if cond != BConst(True):
                    constraints.add(cond)
            else:
                comm_hps.append(
                    (hp.OutputChannel(ch_name="ch_" + out_channel + bran_num, expr=AVar(out_channel)), hp.Skip()))
        # Get evolution domain (contraints) for each ODE
        if len(constraints) == 0:
            constraint = BConst(True)
        else:  # len(constraints) >= 1:
            # Check whether conj(*constraints) is satisfiable
            # by mutually exclusive constraint set of cond_inst
            if sum(set(con_pair).issubset(mu_ex_cons) for mu_ex_cons in cond_inst.mu_ex_cons
                   for con_pair in product(constraints, constraints) if len(set(con_pair)) == 2) >= 1:
                continue  # because cons_pairs contains exclusive constrains
            constraint = conj(*constraints)
        # ode_hps.append(hp.ODE_Comm(eqs=new_ode_eqs, constraint=bexpr_parse(constraint), io_comms=comm_hps))
        ode_hps.append(hp.ODE_Comm(eqs=new_ode_eqs, constraint=constraint, io_comms=comm_hps))

    # ode_hp = hp.ODE_Comm(eqs=ode_eqs, constraint="True", io_comms=comm_hps)
    process = None
    if len(ode_hps) == 1:
        process = hp.Sequence(hp.Sequence(*init_hps), hp.Loop(ode_hps[0]))
    elif len(ode_hps) >= 2:
        process = hp.Sequence(hp.Sequence(*init_hps), hp.Loop(hp.Sequence(*ode_hps)))
    # process.name = "PC" + str(process_num)
    return process


def translate_discrete(diag):
    """Translate the given diagram to an HCSP program."""
    blocks = diag["diag"]
    blocks_dict = {block.name: block for block in blocks}

    # Initialization
    init_hp = hp.Assign(var_name="t", expr=AConst(0))

    # Get input and output channels
    in_ports = diag["in"]
    out_ports = diag["out"]
    in_channels = [hp.InputChannel(ch_name="ch_" + var_name + bran_num, var_name=var_name)
                   for var_name, bran_num in sorted(in_ports)]
    out_channels = [hp.OutputChannel(ch_name="ch_" + expr + bran_num, expr=AVar(expr))
                    for expr, bran_num in sorted(out_ports)]

    # Get discrete processes
    st_cond_inst_dict = dict()  # used for merging the discrete processes with the same sample time
    # discrete_hps = []  # the list of discrete processes
    for block in blocks:
        if not hasattr(block, "st") or block.type == "constant":
            continue

        st_cond = RelExpr(op="==", expr1=ModExpr(expr1=AVar("t"),
                                                 expr2=AConst(block.st)
                                                 if isinstance(block.st, (int, float)) else block.st),
                          expr2=AConst(0))
        if st_cond not in st_cond_inst_dict:
            st_cond_inst_dict[st_cond] = Conditional_Inst()

        # block_hp = None
        in_vars = []
        for line in block.dest_lines:
            if line.src in blocks_dict:
                src_block = blocks_dict[line.src]
                if src_block.type == "constant":
                    in_vars.append(AConst(src_block.value))
                    continue
            in_vars.append(AVar(line.name))
        out_var = block.src_lines[0][0].name
        res_expr = None
        if block.type in ["gain", "bias", "abs", "not"]:  # one input, one output
            if block.type == "gain":
                res_expr = TimesExpr(signs="**", exprs=[in_vars[0], AConst(block.factor)])
            elif block.type == "bias":
                res_expr = PlusExpr(signs="++", exprs=[in_vars[0], AConst(block.bias)])
            elif block.type == "abs":
                res_expr = FunExpr(fun_name="abs", exprs=[in_vars[0]])
            elif block.type == "not":
                res_expr = PlusExpr(signs="+-", exprs=[AConst(1), in_vars[0]])
            # block_hp = hp.Assign(var_name=out_var, expr=res_expr)
            st_cond_inst_dict[st_cond].add(var_name=out_var, cond_inst=[(BConst(True), res_expr)])
        elif block.type in ["add", "divide"]:  # multiple inputs, one output
            assert len(in_vars) == len(block.dest_spec)
            if block.type == "add":
                res_expr = PlusExpr(signs=block.dest_spec, exprs=in_vars)
            elif block.type == "divide":
                res_expr = TimesExpr(signs=block.dest_spec, exprs=in_vars)
            # block_hp = hp.Assign(var_name=out_var, expr=res_expr)
            st_cond_inst_dict[st_cond].add(var_name=out_var, cond_inst=[(BConst(True), res_expr)])
        elif block.type in ["or", "and", "min_max"]:  # multiple inputs, one output
            assert len(in_vars) == block.num_dest
            if block.type == "or":
                res_expr = FunExpr(fun_name="max", exprs=in_vars)
            elif block.type == "and":
                res_expr = FunExpr(fun_name="min", exprs=in_vars)
            elif block.type == "min_max":
                res_expr = FunExpr(fun_name=block.fun_name, exprs=in_vars)
            # block_hp = hp.Assign(var_name=out_var, expr=res_expr)
            st_cond_inst_dict[st_cond].add(var_name=out_var, cond_inst=[(BConst(True), res_expr)])
        elif block.type == "relation":
            cond0 = RelExpr(op=block.relation, expr1=in_vars[0], expr2=in_vars[1])
            # hp0 = hp.Assign(var_name=out_var, expr=AConst(1))
            # cond_hp_0 = hp.Condition(cond=cond0, hp=hp0)
            cond1 = cond0.neg()
            # hp1 = hp.Assign(var_name=out_var, expr=AConst(0))
            # cond_hp_1 = hp.Condition(cond=cond1, hp=hp1)
            # block_hp = hp.Sequence(cond_hp_0, cond_hp_1)
            st_cond_inst_dict[st_cond].add(var_name=out_var, cond_inst=[(cond0, AConst(1)), (cond1, AConst(0))])
        elif block.type == "switch":
            cond0 = RelExpr(op=block.relation, expr1=in_vars[1], expr2=AConst(block.threshold))
            # hp0 = hp.Assign(var_name=out_var, expr=in_vars[0])
            # cond_hp_0 = hp.Condition(cond=cond0, hp=hp0)
            cond2 = cond0.neg()
            # hp2 = hp.Assign(var_name=out_var, expr=in_vars[2])
            # cond_hp_2 = hp.Condition(cond=cond2, hp=hp2)
            # block_hp = hp.Sequence(cond_hp_0, cond_hp_2)
            st_cond_inst_dict[st_cond].add(var_name=out_var, cond_inst=[(cond0, in_vars[0]), (cond2, in_vars[2])])
        elif block.type == "saturation":
            in_var = in_vars[0]
            cond0 = RelExpr(op=">", expr1=in_var, expr2=AConst(block.up_lim))
            # cond_hp_0 = hp.Condition(cond=cond0, hp=hp.Assign(var_name=out_var, expr=AConst(block.up_lim)))
            cond1 = RelExpr(op="<", expr1=in_var, expr2=AConst(block.low_lim))
            # cond_hp_1 = hp.Condition(cond=cond1, hp=hp.Assign(var_name=out_var, expr=AConst(block.low_lim)))
            cond2 = LogicExpr(op="&&", expr1=cond0.neg(), expr2=cond1.neg())
            # block_hp = hp.Sequence(hp.Assign(var_name=out_var, expr=in_var), cond_hp_0, cond_hp_1)
            st_cond_inst_dict[st_cond].add(var_name=out_var, cond_inst=[(cond0, AConst(block.up_lim)),
                                                                        (cond1, AConst(block.low_lim)),
                                                                        (cond2, in_var)])
        # discrete_hps.append(hp.Condition(cond=cond, hp=block_hp))

    # Delete useless (intermidiate) variables in st_cond_inst_dict[st_cond] for each st_cond
    for st_cond, cond_inst in st_cond_inst_dict.items():
        outport_vars = set(expr for expr, _ in out_ports)
        in_var_others = set()  # the set of input variables of other groups of processes
        for other_cond, other_inst in st_cond_inst_dict.items():
            if st_cond != other_cond:
                for cond_expr_list in other_inst.data.values():
                    for cond, expr in cond_expr_list:
                        in_var_others = in_var_others.union(cond.get_vars(), expr.get_vars())
        useful_vars = outport_vars.union(set(cond_inst.data.keys()).intersection(in_var_others))
        useless_vars = set(cond_inst.data.keys()) - useful_vars
        for var in useless_vars:
            del cond_inst.data[var]
    # Get discrete processes
    discrete_hps = []
    for st_cond, cond_inst in st_cond_inst_dict.items():
        processes = []
        for var, cond_expr_list in cond_inst.data.items():
            if len(cond_expr_list) == 1:
                processes.append(hp.Assign(var_name=var, expr=cond_expr_list[0][1]))
            else:  # len(cond_expr_list) >= 2:
                for cond, expr in cond_expr_list:
                    processes.append(hp.Condition(cond=cond, hp=hp.Assign(var_name=var, expr=expr)))
        if len(processes) == 1:
            discrete_hps.append(hp.Condition(cond=st_cond, hp=processes[0]))
        else:
            discrete_hps.append(hp.Condition(cond=st_cond, hp=hp.Sequence(*processes)))

    # Get the time process
    # Compute the GCD of sample times of all the discrete blocks
    known_st = []
    unknown_st = []
    for block in blocks:
        if isinstance(block.st, (int, float)):
            assert block.st > -1
            known_st.append(block.st)
        else:
            assert isinstance(block.st, (AVar, FunExpr))
            unknown_st.append(AVar(block.name))

    if known_st:
        known_st = [AConst(get_gcd(known_st))]
    known_st.extend(unknown_st)
    st_gcd = FunExpr(fun_name="gcd", exprs=known_st) if len(known_st) >= 2 else known_st[0]

    # Get loop body
    loop_hps = in_channels + discrete_hps + out_channels + \
               [hp.Wait(delay=st_gcd), hp.Assign(var_name="t", expr=PlusExpr(signs="++", exprs=[AVar("t"), st_gcd]))]
    loop_hps = hp.Sequence(*loop_hps)
    process = hp.Sequence(init_hp, hp.Loop(loop_hps))
    return process


def seperate_diagram(blocks_dict):
    """Seperate a diagram into discrete and continous subdiagrams."""
    # delete in and out-ports
    blocks_dict = {name: block for name, block in blocks_dict.items() if block.type not in ['in_port', 'out_port']}

    # Seperating: search SCC by BFS
    discrete_subdiagrams = []
    continuous_subdiagrams = []
    while blocks_dict:
        _, block = blocks_dict.popitem()
        scc = [block]
        bs = [block]
        while bs:
            b = bs.pop()
            for src_line in b.src_lines:
                for line in src_line:
                    dest_name = line.dest
                    if dest_name in blocks_dict and blocks_dict[dest_name].is_continuous == block.is_continuous:
                        bs.append(blocks_dict[dest_name])
                        scc.append(blocks_dict[dest_name])
                        del blocks_dict[dest_name]
            for dest_line in b.dest_lines:
                src_name = dest_line.src
                if src_name in blocks_dict and blocks_dict[src_name].is_continuous == block.is_continuous:
                    bs.append(blocks_dict[src_name])
                    scc.append(blocks_dict[src_name])
                    del blocks_dict[src_name]
        if block.is_continuous:
            continuous_subdiagrams.append(scc)
        else:
            discrete_subdiagrams.append(scc)
    # print("D:" + str(discrete_subdiagrams))
    # print("C" + str(continuous_subdiagrams))

    # Sorting: for disrecte blocks
    discrete_subdiagrams_sorted = []
    for scc in discrete_subdiagrams:
        scc_dict = {block.name: block for block in scc}
        sorted_scc = []
        while scc_dict:
            delete_blocks = []
            for block in scc_dict.values():
                src_set = set()
                for dest_line in block.dest_lines:
                    src_set.add(dest_line.src)
                if src_set.isdisjoint(set(scc_dict.keys())):
                    sorted_scc.append(block)
                    delete_blocks.append(block.name)
            for block_name in delete_blocks:
                del scc_dict[block_name]
        discrete_subdiagrams_sorted.append(sorted_scc)

    # Get input and output channels
    continuous_groups = [[block.name for block in scc] for scc in continuous_subdiagrams]

    dis_subdiag_with_chs = []
    for sorted_scc in discrete_subdiagrams_sorted:
        in_channels = set()
        out_channels = set()
        block_names = [block.name for block in sorted_scc]
        for block in sorted_scc:
            for dest_line in block.dest_lines:
                if dest_line.src not in block_names:  # an input channel
                    in_channels.add((dest_line.name, ""))  # (var_name, branch_num)
            for src_lines in block.src_lines:  # Each group represents a variable
                channel_groups = {}
                for src_line in src_lines:
                    if src_line.dest not in block_names:  # an output channel
                        is_outport = True  # if src_line.dest is an outport
                        for i in range(len(continuous_groups)):
                            if src_line.dest in continuous_groups[i]:
                                is_outport = False
                                if i not in channel_groups:
                                    channel_groups[i] = []
                                channel_groups[i].append(src_line.branch)
                                break
                        if is_outport:
                            out_channels.add((src_line.name, "_" + str(src_line.branch)))
                for channels in channel_groups.values():
                    out_channels.add((src_lines[0].name, "_" + str(min(channels))))
        dis_subdiag_with_chs.append({"in": in_channels, "diag": sorted_scc, "out": out_channels})

    con_subdiag_with_chs = []
    for scc in continuous_subdiagrams:
        in_channels = set()
        out_channels = set()
        block_names = [block.name for block in scc]
        channel_groups = {}
        for block in scc:
            for dest_line in block.dest_lines:
                if dest_line.src not in block_names:  # an input channel
                    if dest_line.name not in channel_groups:
                        channel_groups[dest_line.name] = []
                    channel_groups[dest_line.name].append(dest_line.branch)
            for src_lines in block.src_lines:
                for src_line in src_lines:
                    if src_line.dest not in block_names:  # an output channel
                        out_channels.add((src_line.name, ""))
        for channel, branches in channel_groups.items():
            in_channels.add((channel, "_" + str(min(branches))))
        con_subdiag_with_chs.append({"in": in_channels, "diag": scc, "out": out_channels})

    # return discrete_subdiagrams_sorted, continuous_subdiagrams
    return dis_subdiag_with_chs, con_subdiag_with_chs


def get_processes(dis_subdiag_with_chs, con_subdiag_with_chs):
    """Compute the discrete and continuous processes from a diagram,
    which is represented as discrete and continuous subdiagrams."""
    processes = hp.HCSPProcess()
    main_processes = []
    # Compute the discrete processes from discrete subdiagrams
    num = 0
    for diag in dis_subdiag_with_chs:
        name = "PD" + str(num)
        discrete_process = translate_discrete(diag)
        processes.add(name, discrete_process)
        main_processes.append(hp.Var(name))
        num += 1

    # Compute the continuous processes from continuous subdiagrams
    num = 0
    for diag in con_subdiag_with_chs:
        name = "PC" + str(num)
        continuous_process = translate_continuous(diag)
        processes.add(name, continuous_process)
        main_processes.append(hp.Var(name))
        num += 1

    # Get main paralell processes
    assert len(main_processes) >= 1
    main_process = hp.Parallel(*main_processes) if len(main_processes) >= 2 else main_processes[0]
    processes.insert(n=0, name="P", hp=main_process)

    return processes


def delete_subsystems(blocks_dict):
    subsystems = []
    blocks_in_subsystems = []
    for block in blocks_dict.values():
        if block.type == "subsystem":
            # Collect all the subsystems to be deleted
            subsystems.append(block.name)
            # The subsytem is treated as a diagram
            subsystem = block.diagram
            # Delete subsystems recursively
            delete_subsystems(subsystem.blocks_dict)
            # Move all the blocks except ports from the subsystem to the parent system
            for sub_block in subsystem.blocks_dict.values():
                if sub_block.type not in ["in_port", "out_port"]:
                    blocks_in_subsystems.append(sub_block)
            # Sort the input ports in the subsystem by names
            input_ports = [sub_block for sub_block in subsystem.blocks if sub_block.type == "in_port"]
            input_ports.sort(key=operator.attrgetter('name'))
            # Sort the output ports in the subsystem by names
            output_ports = [sub_block for sub_block in subsystem.blocks if sub_block.type == "out_port"]
            output_ports.sort(key=operator.attrgetter('name'))

            # Delete old input lines and add new ones
            for port_id in range(block.num_dest):
                input_line = block.dest_lines[port_id]

                # src_block = blocks_dict[input_line.src]
                if input_line.src in blocks_dict:
                    src_block = blocks_dict[input_line.src]
                else:
                    for subsys in subsystems:
                        if input_line.src in blocks_dict[subsys].diagram.blocks_dict:
                            src_block = blocks_dict[subsys].diagram.blocks_dict[input_line.src]
                            break

                # Delete the old line (input_line) from src_block
                src_block.src_lines[input_line.src_port][input_line.branch] = None
                # Get the corresponding input port in the subsystem
                port = input_ports[port_id]
                assert port.name == "in_" + str(port_id)
                for port_line in port.src_lines[0]:
                    dest_block = subsystem.blocks_dict[port_line.dest]
                    # Generate a new input line
                    new_input_line = SL_Line(src=src_block.name, dest=dest_block.name,
                                             src_port=input_line.src_port, dest_port=port_line.dest_port)
                    new_input_line.name = input_line.name
                    # Delete the old line (port_line) and add a new one
                    dest_block.add_dest(port_id=port_line.dest_port, sl_line=new_input_line)
                    # Add a new line for src_block
                    src_block.add_src(port_id=input_line.src_port, sl_line=new_input_line)

            # Delete old output lines and add new ones
            for port_id in range(block.num_src):
                # Get the corresponding output port in the subsystem
                port = output_ports[port_id]
                assert port.name == "out_" + str(port_id)
                port_line = port.dest_lines[0]
                src_block = subsystem.blocks_dict[port_line.src]
                # Delete the old line (port_line) from src_block
                src_block.src_lines[port_line.src_port][port_line.branch] = None
                for output_line in block.src_lines[port_id]:

                    # dest_block = blocks_dict[output_line.dest]
                    if output_line.dest in blocks_dict:
                        dest_block = blocks_dict[output_line.dest]
                    else:
                        for subsys in subsystems:
                            if output_line.dest in blocks_dict[subsys].diagram.blocks_dict:
                                dest_block = blocks_dict[subsys].diagram.blocks_dict[output_line.dest]
                                break

                    # Generate a new output line
                    new_output_line = SL_Line(src=src_block.name, dest=dest_block.name,
                                              src_port=port_line.src_port, dest_port=output_line.dest_port)
                    new_output_line.name = output_line.name
                    # Delete the old line (output_line) and add a new one
                    dest_block.add_dest(port_id=output_line.dest_port, sl_line=new_output_line)
                    # Add a new line for src_block
                    src_block.add_src(port_id=port_line.src_port, sl_line=new_output_line)

    # Delete all the subsystems
    for name in subsystems:
        del blocks_dict[name]
    # Add new blocks from subsystems to block_dict
    for block in blocks_in_subsystems:
        assert block.name not in blocks_dict
        blocks_dict[block.name] = block
