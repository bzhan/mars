from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.sl.system import System
from ss2hcsp.sl.sl_line import SL_Line
# from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.expr import *
# from ss2hcsp.hcsp.parser import aexpr_parser, bexpr_parser

from functools import reduce
from math import gcd
import re
import operator
from itertools import product


def translate_continuous(blocks):
    """Translate the given diagram to an HCSP program."""

    """Some stateless blocks, such as add and gain, are treated as
    continuous here, so we have to delete these blocks and subsititue
    the corresponding variables."""
    # Get non-continuous blocks from blocks_dict
    non_con_blocks = {block.name: block for block in blocks if block.type not in ("integrator", "constant")}
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
                if block.type in ["gain", "bias", "abs", "not"]:  # One input, one output
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
                elif block.type in ["add", "divide", "min_max"]:  # Multiple inputs, one output
                    assert len(in_vars) == len(block.dest_spec)
                    exprs = [AVar(var) for var in in_vars]
                    if block.type == "add":
                        res_expr = PlusExpr(signs=block.dest_spec, exprs=exprs)
                    elif block.type == "divide":
                        res_expr = TimesExpr(signs=block.dest_spec, exprs=exprs)
                    elif block.type == "min_max":
                        res_expr = FunExpr(fun_name=block.fun_name, exprs=exprs)
                    cond_inst.add(var_name=out_var, cond_inst=[(BConst(True), res_expr)])
                elif block.type in ["or", "and"]:  # Logic expressions
                    if block.type == "or":
                        res_expr = FunExpr(fun_name="max", exprs=[AVar(var) for var in in_vars])
                    elif block.type == "and":
                        res_expr = FunExpr(fun_name="min", exprs=[AVar(var) for var in in_vars])
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
                    cond2 = LogicExpr(op="&&", expr1=RelExpr(op="<=", expr1=AVar(in_var), expr2=AConst(block.up_lim)),
                                      expr2=RelExpr(op=">=", expr1=AVar(in_var), expr2=AConst(block.low_lim)))
                    cond_inst.add(var_name=out_var, cond_inst=[(cond0, AConst(block.up_lim)),
                                                               (cond1, AConst(block.low_lim)),
                                                               (cond2, AVar(in_var))])
                delete_block.append(block.name)
        for name in delete_block:
            del non_con_blocks[name]

    """Get differential equations"""
    # Initial values for variables
    init_hps = []
    ode_eqs = []
    for block in blocks:
        if block.type == "integrator":
            src_name = block.src_lines[0][0].name
            # init_hps.append(hp.Assign(var_name=src_name, expr=aexpr_parse(block.init_value)))
            init_hps.append(hp.Assign(var_name=src_name, expr=AConst(block.init_value)))
            dest_name = block.dest_lines[0].name
            ode_eqs.append((src_name, AVar(dest_name)))
        elif block.type == "constant":
            src_name = block.src_lines[0][0].name
            init_hps.append(hp.Assign(var_name=src_name, expr=AConst(block.value)))
            ode_eqs.append((src_name, AConst(0)))

    init_hps.append(hp.Assign(var_name="t", expr=AConst(0)))
    ode_eqs.append(("t", AConst(1)))

    # Add communication for each port
    in_channels = set()
    out_channels = set()
    block_names = [block.name for block in blocks]
    for block in blocks:
        for dest_line in block.dest_lines:
            if dest_line.src not in block_names:
                in_channels.add(dest_line.name)
        for src_lines in block.src_lines:
            for src_line in src_lines:
                if src_line.dest not in block_names:
                    out_channels.add(src_line.name)

    # Delete useless variables in cond_inst.data
    in_var_ode = set(in_var.name for _, in_var in ode_eqs if hasattr(in_var, "name"))  # isinstance(in_var, AVar)
    delete_vars = [var for var in cond_inst.data.keys() if var not in in_var_ode.union(out_channels)]
    for var in delete_vars:
        del cond_inst.data[var]
    # delete_vars = [var for var in var_dict.keys() if var not in in_var_ode.union(out_channels)]
    # for var in delete_vars:
    #     del var_dict[var]

    """Substitute variables in the ODEs by cond_inst.data"""
    # var_cond_exprs = [(var, cond_exprs) for var, cond_exprs in var_dict.items()]
    var_cond_exprs = [(var, cond_exprs) for var, cond_exprs in cond_inst.data.items()]
    var_list = [e[0] for e in var_cond_exprs]  # e[0] is a variable name
    cond_exprs_list = [e[1] for e in var_cond_exprs]  # e[1] is the list of (condition, expression) pairs wrt. e[0]
    if len(var_list) == 0:  # Do not need to substitute
        in_channel_hps = [(hp.InputChannel(var_name=var_name), hp.Skip())
                          for var_name in sorted(in_channels)]
        out_channel_hps = [(hp.OutputChannel(expr=AVar(var_name)), hp.Skip())
                           for var_name in sorted(out_channels)]
        comm_hps = in_channel_hps + out_channel_hps
        ode_hp = hp.ODE_Comm(eqs=ode_eqs, constraint=BConst(True), io_comms=comm_hps)
        return hp.Sequence(hp.Sequence(*init_hps), hp.Loop(ode_hp))
    # if len(var_list) == 1:  # len(cond_exprs_list) == 1
    #     compositions = [[e] for e in cond_exprs_list[0]]
    else:  # len(var_list) >= 2
        # compositions = reduce(cartesian_product, cond_exprs_list)
        compositions = product(*cond_exprs_list)
    ode_hps = []
    for composition in compositions:
        new_ode_eqs = []
        constraints = set()
        # constraints.add("True")
        comm_hps = [(hp.InputChannel(ch_name="ch_" + var_name, var_name=var_name), hp.Skip())
                    for var_name in sorted(in_channels)]
        for out_var, in_var in ode_eqs:  # isinstance(out_var, str) and isinstance(in_var, AVar)
            if hasattr(in_var, "name") and in_var.name in var_list:
                cond = composition[var_list.index(in_var.name)][0]
                _expr = composition[var_list.index(in_var.name)][1]
                # new_ode_eqs.append((out_var, aexpr_parse(expr)))
                new_ode_eqs.append((out_var, _expr))
                constraints.add(cond)
            else:
                new_ode_eqs.append((out_var, in_var))
        # print("new_ode_eqs = ", new_ode_eqs)
        for out_channel in sorted(out_channels):
            # print("ch_" + out_channel + "!")
            if out_channel in var_list:
                cond = composition[var_list.index(out_channel)][0]
                _expr = composition[var_list.index(out_channel)][1]
                comm_hps.append((hp.OutputChannel(ch_name="ch_" + out_channel, expr=_expr), hp.Skip()))
                # comm_hps.append((hp.OutputChannel(var_name=out_channel, expr=aexpr_parse(expr)), hp.Skip()))
                constraints.add(cond)
                # print(expr)
            else:
                comm_hps.append((hp.OutputChannel(ch_name="ch_" + out_channel, expr=AVar(out_channel)), hp.Skip()))
        # Get evolution domain (contraints) for each ODE
        # constraint = "True"
        # constraints.remove("True")
        # print("constrains = ", constraints)
        if len(constraints) == 0:
            # constraint = constraints.pop()
            constraint = BConst(True)
        else:  # len(constraints) >= 1:
            # constraint = "&&".join(constraints)
            constraint = conj(*constraints)
        # print("constrain = ", constraint)
        # print("comm_hps", comm_hps)
        # print("-" * 50)
        # ode_hps.append(hp.ODE_Comm(eqs=new_ode_eqs, constraint=bexpr_parse(constraint), io_comms=comm_hps))
        ode_hps.append(hp.ODE_Comm(eqs=new_ode_eqs, constraint=constraint, io_comms=comm_hps))

    # ode_hp = hp.ODE_Comm(eqs=ode_eqs, constraint="True", io_comms=comm_hps)
    if len(ode_hps) == 1:
        process = hp.Sequence(hp.Sequence(*init_hps), hp.Loop(ode_hps[0]))
    else:  # len(ode_hps) >= 2
        process = hp.Sequence(hp.Sequence(*init_hps), hp.Loop(hp.Sequence(*ode_hps)))
    # process.name = "PC" + str(process_num)
    return process


def translate_discrete(blocks):
    """Translate the given diagram to an HCSP program."""
    # Initialization
    init_hp = hp.Assign(var_name="t", expr=AConst(0))

    # Get input and output channels
    in_ports = set()
    out_ports = set()
    block_names = [block.name for block in blocks]
    for block in blocks:
        for dest_line in block.dest_lines:
            if dest_line.src not in block_names:
                in_ports.add(dest_line.name)
        for src_lines in block.src_lines:
            for src_line in src_lines:
                if src_line.dest not in block_names:
                    out_ports.add(src_line.name)
    in_channels = [hp.InputChannel(ch_name="ch_" + var_name, var_name=var_name) for var_name in sorted(in_ports)]
    out_channels = [hp.OutputChannel(ch_name="ch_" + expr, expr=AVar(expr)) for expr in sorted(out_ports)]

    # Get discrete processes
    discrete_hps = []
    for block in blocks:
        if not hasattr(block, "st"):
            continue
        # cond = "t%" + block.st + "==0"
        cond = RelExpr(op="==", expr1=ModExpr(expr1=AVar("t"),
                                              expr2=AConst(block.st) if isinstance(block.st, int) else block.st),
                       expr2=AConst(0))
        block_hp = None
        in_vars = [line.name for line in block.dest_lines]
        out_var = block.src_lines[0][0].name
        res_expr = None
        if block.type in ["gain", "bias", "abs", "not", "unit_delay"]:  # one input, one output
            in_var = in_vars[0]
            if block.type == "gain":
                res_expr = TimesExpr(signs="**", exprs=[AVar(in_var), AConst(block.factor)])
            elif block.type == "bias":
                res_expr = PlusExpr(signs="++", exprs=[AVar(in_var), AConst(block.bias)])
            elif block.type == "abs":
                res_expr = FunExpr(fun_name="abs", exprs=[AVar(in_var)])
            elif block.type == "not":
                res_expr = PlusExpr(signs="+-", exprs=[AConst(1), AVar(in_var)])
            elif block.type == "unit_delay":
                res_expr = FunExpr(fun_name="delay", exprs=[AVar(in_var), AConst(block.st)])
            block_hp = hp.Assign(var_name=out_var, expr=res_expr)
        elif block.type in ["add", "divide", "min_max"]:  # multiple inputs, one output
            assert len(in_vars) == len(block.dest_spec)
            exprs = [AVar(var) for var in in_vars]
            if block.type == "add":
                res_expr = PlusExpr(signs=block.dest_spec, exprs=exprs)
            elif block.type == "divide":
                res_expr = TimesExpr(signs=block.dest_spec, exprs=exprs)
            elif block.type == "min_max":
                res_expr = FunExpr(fun_name=block.fun_name, exprs=exprs)
            block_hp = hp.Assign(var_name=out_var, expr=res_expr)
        elif block.type in ["or", "and"]:
            if block.type == "or":
                res_expr = FunExpr(fun_name="max", exprs=[AVar(var) for var in in_vars])
            elif block.type == "and":
                res_expr = FunExpr(fun_name="min", exprs=[AVar(var) for var in in_vars])
            block_hp = hp.Assign(var_name=out_var, expr=res_expr)
        elif block.type == "relation":
            cond0 = RelExpr(op=block.relation, expr1=AVar(in_vars[0]), expr2=AVar(in_vars[1]))
            hp0 = hp.Assign(var_name=out_var, expr=AConst(1))
            cond_hp_0 = hp.Condition(cond=cond0, hp=hp0)
            cond1 = cond0.neg()
            hp1 = hp.Assign(var_name=out_var, expr=AConst(0))
            cond_hp_1 = hp.Condition(cond=cond1, hp=hp1)
            block_hp = hp.Sequence(cond_hp_0, cond_hp_1)
        elif block.type == "switch":
            cond0 = RelExpr(op=block.relation, expr1=AVar(in_vars[1]), expr2=AConst(block.threshold))
            hp0 = hp.Assign(var_name=out_var, expr=AVar(in_vars[0]))
            cond_hp_0 = hp.Condition(cond=cond0, hp=hp0)
            cond2 = cond0.neg()
            hp2 = hp.Assign(var_name=out_var, expr=AVar(in_vars[2]))
            cond_hp_2 = hp.Condition(cond=cond2, hp=hp2)
            block_hp = hp.Sequence(cond_hp_0, cond_hp_2)
        elif block.type == "saturation":
            in_var = in_vars[0]
            cond0 = RelExpr(op=">", expr1=AVar(in_var), expr2=AConst(block.up_lim))
            cond_hp_0 = hp.Condition(cond=cond0, hp=hp.Assign(var_name=out_var, expr=AConst(block.up_lim)))
            cond1 = RelExpr(op="<", expr1=AVar(in_var), expr2=AConst(block.low_lim))
            cond_hp_1 = hp.Condition(cond=cond1, hp=hp.Assign(var_name=out_var, expr=AConst(block.low_lim)))
            block_hp = hp.Sequence(hp.Assign(var_name=out_var, expr=AVar(in_var)), cond_hp_0, cond_hp_1)

        discrete_hps.append(hp.Condition(cond=cond, hp=block_hp))

    # Get the time process
    # Compute the GCD of sample times of all the discrete blocks
    known_st = []
    unknown_st = []
    for block in blocks:
        if hasattr(block, "st") and re.match("\\d+", str(block.st)):
            known_st.append(block.st)
        elif hasattr(block, "st"):
            unknown_st.append(AVar(block.name))
    if known_st:
        known_st = [AConst(reduce(gcd, known_st) if len(known_st) >= 2 else known_st[0])]
    known_st.extend(unknown_st)
    st_gcd = FunExpr(fun_name="gcd", exprs=known_st) if len(known_st) >= 2 else known_st[0]
    temp = hp.Assign(var_name="temp", expr=AVar("t"))
    time_ode = hp.ODE(eqs=[("t", AConst(1))],
                      constraint=RelExpr(op="<", expr1=AVar("t"),
                                         expr2=PlusExpr(signs="++", exprs=[AVar("temp"), st_gcd])))
    time_processes = [temp, time_ode]
    # Get loop body
    loop_hps = in_channels + discrete_hps + out_channels + time_processes
    # loop_body = loop_hps[0]
    # for i in range(1, len(loop_hps)):
    #     loop_body = hp.Sequence(loop_body, loop_hps[i])
    # process = hp.Sequence(init_hp, hp.Loop(loop_body))
    loop_hps = hp.Sequence(*loop_hps)
    process = hp.Sequence(init_hp, hp.Loop(loop_hps))
    return process


def seperate_diagram(blocks_dict):
    """Seperate a diagram into discrete and continous subdiagrams."""
    blocks_dict = blocks_dict.copy()

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
    # print("sorted = ", discrete_subdiagrams_sorted)
    return discrete_subdiagrams_sorted, continuous_subdiagrams


def get_processes(discrete_subdiagrams_sorted, continuous_subdiagrams):
    """Compute the discrete and continuous processes from a diagram,
    which is represented as discrete and continuous subdiagrams."""
    system = System()
    # Compute the discrete processes from discrete subdiagrams
    num = 0
    for scc in discrete_subdiagrams_sorted:
        discrete_process = translate_discrete(scc)
        discrete_process.name = "PD" + str(num)
        system.discrete_processes.append(discrete_process)
        num += 1

    # Compute the continuous processes from continuous subdiagrams
    num = 0
    for scc in continuous_subdiagrams:
        continuous_process = translate_continuous(scc)
        continuous_process.name = "PC" + str(num)
        system.continuous_processes.append(continuous_process)
        num += 1

    return system


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
                src_block = blocks_dict[input_line.src]
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
                    dest_block = blocks_dict[output_line.dest]
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
        assert block not in blocks_dict
        blocks_dict[block.name] = block
