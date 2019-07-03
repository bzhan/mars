from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.sl.system import System
from ss2hcsp.sl.sl_line import SL_Line

from functools import reduce
from math import gcd
import re
import operator


def cartesian_product(list0, list1):
    assert len(list0) >= 1 and len(list1) >= 1
    # Lift
    if not isinstance(list0[0], list):
        list0 = [[e] for e in list0]
    if not isinstance(list1[0], list):
        list1 = [[e] for e in list1]
    return [e0 + e1 for e0 in list0 for e1 in list1]


def variable_subsitution(var_dict, out_var, cond_expr):
    """out_var is the variable expressed by cond_expr, a list of (condition, expression) pairs.
    Before putting out_var: con_expr into the dictionary var_dict, the variable substituion
    should be performed."""
    """For the facility of substituting variables, all the variables
    are surrounded by square brackets, such as [x]."""
    assert out_var not in var_dict
    if var_dict:
        for var_name in var_dict.keys():
            new_cond_expr = []  # the updated cond_expr
            for (cond, expr) in cond_expr:
                if cond.find(var_name) != -1 or expr.find(var_name) != -1:
                    for (cond_v, expr_v) in var_dict[var_name]:
                        new_cond = re.sub(var_name, expr_v, cond)
                        if cond_v != "True" and new_cond != "True":
                            new_cond = cond_v + "&&" + new_cond
                        elif cond_v != "True":  # new_cond == "True"
                            new_cond = cond_v
                        new_expr = re.sub(var_name, expr_v, expr)
                        new_cond_expr.append((new_cond, new_expr))
                else:
                    new_cond_expr.append((cond, expr))
            cond_expr = new_cond_expr

        # Merge the (condition, expression) pairs in new_cond_expr with the same expression
        expr_conds = {}
        for (cond, expr) in cond_expr:
            if expr not in expr_conds:
                expr_conds[expr] = [cond]
            else:
                expr_conds[expr].append(cond)
        cond_expr = []
        for expr, conds in expr_conds.items():
            if len(conds) == 1:
                cond_expr.append((conds[0], expr))
            else:  # len(conds) >= 2
                cond_expr.append(("||".join(conds), expr))
    var_dict[out_var] = cond_expr
    # print(var_dict)
    # if len(var_dict) >= 2:
    #     print(var_dict.keys())
    #     print(reduce(cartesian_product, var_dict.values()))


def translate_continuous(blocks):
    """Translate the given diagram to an HCSP program."""

    """Some stateless blocks, such as add and gain, are treated as
    continuous here, so we have to delete these blocks and subsititue
    the corresponding varaibles."""
    # Get non-continuous blocks from blocks_dict
    non_con_blocks = {block.name: block for block in blocks if block.type not in ("integrator", "constant")}
    var_dict = {}  # dictionary for varianble substituting
    while non_con_blocks:
        delete_block = []
        for block in non_con_blocks.values():
            src_set = set()
            for dest_line in block.dest_lines:
                src_set.add(dest_line.src)
            if src_set.isdisjoint(set(non_con_blocks.keys())):
                in_vars = [line.name for line in block.dest_lines]  # keep the order?
                out_var = block.src_lines[0][0].name
                expr = None
                if block.type in ["gain", "bias", "abs", "not"]:
                    in_var = in_vars[0]
                    if block.type == "gain":
                        if block.factor.startswith("-"):
                            expr = in_var + "*(" + block.factor + ")"
                        else:
                            expr = in_var + "*" + block.factor
                    elif block.type == "bias":
                        if block.bias.startswith("-"):
                            expr = in_var + block.bias
                        else:
                            expr = in_var + "+" + block.bias
                    elif block.type == "abs":
                        expr = "abs(" + in_var + ")"
                    elif block.type == "not":
                        expr = "1-" + in_var
                    variable_subsitution(var_dict, out_var, [("True", expr)])
                elif block.type in ["add", "divide"]:
                    assert len(in_vars) == len(block.dest_spec)
                    # Get the head of the expression
                    expr = in_vars[0]
                    if block.dest_spec[0] == "-":
                        expr = "-" + expr
                    elif block.dest_spec[0] == "/":
                        expr = "1/" + expr
                    for i in range(1, len(block.dest_spec)):
                        expr = expr + block.dest_spec[i] + in_vars[i]
                    variable_subsitution(var_dict, out_var, [("True", expr)])
                elif block.type in ["or", "and"]:
                    if block.type == "or":
                        expr = "max(" + ", ".join(in_vars) + ")"
                    elif block.type == "and":
                        expr = "min(" + ", ".join(in_vars) + ")"
                    variable_subsitution(var_dict, out_var, [("True", expr)])
                elif block.type == "relation":
                    expr = block.relation.join(in_vars)
                    variable_subsitution(var_dict, out_var, [("True", expr)])
                elif block.type == "switch":
                    cond0 = in_vars[1] + block.relation + block.threshold
                    cond2 = in_vars[1] + block.neg_relation + block.threshold
                    variable_subsitution(var_dict, out_var, [(cond0, in_vars[0]), (cond2, in_vars[2])])
                delete_block.append(block.name)
        for name in delete_block:
            del non_con_blocks[name]
    # return var_dict

    # Initial values for variables
    init_hps = []
    # Differential equation
    ode_eqs = []
    for block in blocks:
        if block.type == "integrator":
            src_name = block.src_lines[0][0].name
            init_hps.append(hp.Assign(var_name=src_name, expr=block.init_value))
            dest_name = block.dest_lines[0].name
            ode_eqs.append((src_name, dest_name))
        elif block.type == "constant":
            src_name = block.src_lines[0][0].name
            init_hps.append(hp.Assign(var_name=src_name, expr=block.value))
            ode_eqs.append((src_name, "0"))

    init_hps.append(hp.Assign(var_name="t", expr="0"))
    ode_eqs.append(("t", "1"))

    # Add communication for each port
    # comm_hps = []
    # for block in blocks:
    #     if block.type == 'in_port':
    #         src_name = block.src_lines[0][0].name
    #         comm_hps.append((hp.InputChannel(var_name=src_name), hp.Skip()))
    #     elif block.type == 'out_port':
    #         dest_name = block.dest_lines[0].name
    #         comm_hps.append((hp.OutputChannel(expr=dest_name), hp.Skip()))
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
    in_var_ode = set(in_var for _, in_var in ode_eqs)
    # Delete useless variables
    delete_vars = [var for var in var_dict.keys() if var not in in_var_ode.union(out_channels)]
    for var in delete_vars:
        del var_dict[var]
    var_cond_exprs = [(var, cond_exprs) for var, cond_exprs in var_dict.items()]
    var_list = [e[0] for e in var_cond_exprs]  # e[0] is a variable name
    cond_exprs_list = [e[1] for e in var_cond_exprs]  # e[1] is the list of (condition, expression) pairs wrt. e[0]
    if len(var_list) == 0:  # Do not need to substitute
        in_channel_hps = [(hp.InputChannel(var_name=var_name), hp.Skip()) for var_name in sorted(in_channels)]
        out_channel_hps = [(hp.OutputChannel(expr=var_name), hp.Skip()) for var_name in sorted(out_channels)]
        comm_hps = in_channel_hps + out_channel_hps
        ode_hp = hp.ODE_Comm(eqs=ode_eqs, constraint="True", io_comms=comm_hps)
        return hp.Sequence(hp.Sequence(*init_hps), hp.Loop(ode_hp))
    if len(var_list) == 1:  # len(cond_exprs_list) == 1
        compositions = [[e] for e in cond_exprs_list[0]]
    else:  # len(var_list) >= 2
        compositions = reduce(cartesian_product, cond_exprs_list)
    ode_hps = []
    for composition in compositions:
        new_ode_eqs = []
        constraints = set()
        constraints.add("True")
        comm_hps = [(hp.InputChannel(var_name=var_name), hp.Skip()) for var_name in sorted(in_channels)]
        for out_var, in_var in ode_eqs:
            if in_var in var_list:
                cond = composition[var_list.index(in_var)][0]
                expr = composition[var_list.index(in_var)][1]
                new_ode_eqs.append((out_var, expr))
                constraints.add(cond)
            else:
                new_ode_eqs.append((out_var, in_var))
        # print("new_ode_eqs = ", new_ode_eqs)
        for out_channel in out_channels:
            # print("ch_" + out_channel + "!")
            if out_channel in var_list:
                cond = composition[var_list.index(out_channel)][0]
                expr = composition[var_list.index(out_channel)][1]
                comm_hps.append((hp.OutputChannel(var_name=out_channel, expr=expr), hp.Skip()))
                constraints.add(cond)
                # print(expr)
            else:
                comm_hps.append((hp.OutputChannel(expr=out_channel), hp.Skip()))
                # print(out_channel)
        constraint = "True"
        constraints.remove("True")
        # print("constrains = ", constraints)
        if len(constraints) == 1:
            constraint = constraints.pop()
        elif len(constraints) >= 2:
            constraint = "&&".join(constraints)
        # print("constrain = ", constraint)
        # print("comm_hps", comm_hps)
        # print("-" * 50)
        ode_hps.append(hp.ODE_Comm(eqs=new_ode_eqs, constraint=constraint, io_comms=comm_hps))

    # ode_hp = hp.ODE_Comm(eqs=ode_eqs, constraint="True", io_comms=comm_hps)
    process = hp.Sequence(hp.Sequence(*init_hps), hp.Loop(hp.Sequence(*ode_hps)))
    # process.name = "PC" + str(process_num)
    return process


def translate_discrete(blocks):
    """Translate the given diagram to an HCSP program."""
    # Initialization
    init_hp = hp.Assign(var_name="t", expr="0")

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
    in_channels = [hp.InputChannel(var_name=var_name) for var_name in sorted(in_ports)]
    out_channels = [hp.OutputChannel(expr=expr) for expr in sorted(out_ports)]

    # Get discrete processes
    discrete_hps = []
    for block in blocks:
        if not hasattr(block, "st"):
            continue
        cond = "t%" + block.st + "==0"
        block_hp = None
        in_vars = [line.name for line in block.dest_lines]  # keep the order?
        out_var = block.src_lines[0][0].name
        if block.type in ["gain", "bias", "abs", "not"]:
            in_var = in_vars[0]
            block_hp = None
            if block.type == "gain":
                if block.factor.startswith("-"):
                    expr = in_var + "*(" + block.factor + ")"
                else:
                    expr = in_var + "*" + block.factor
                block_hp = hp.Assign(var_name=out_var, expr=expr)
            elif block.type == "bias":
                if block.bias.startswith("-"):
                    expr = in_var + block.bias
                else:
                    expr = in_var + "+" + block.bias
                block_hp = hp.Assign(var_name=out_var, expr=expr)
            elif block.type == "abs":
                # cond_hp1 = hp.Condition(cond=in_var + ">=0", hp=hp.Assign(var_name=out_var, expr=in_var))
                # cond_hp2 = hp.Condition(cond=in_var + "<0", hp=hp.Assign(var_name=out_var, expr="-" + in_var))
                # block_hp = hp.Sequence(cond_hp1, cond_hp2)
                block_hp = hp.Assign(var_name=out_var, expr="abs(" + in_var + ")")
            elif block.type == "not":
                block_hp = hp.Assign(var_name=out_var, expr="1-" + in_var)
        elif block.type in ["add", "divide"]:
            assert len(in_vars) == len(block.dest_spec)
            # Get the head of the expression
            expr = in_vars[0]
            if block.dest_spec[0] == "-":
                expr = "-" + expr
            elif block.dest_spec[0] == "/":
                expr = "1/" + expr
            for i in range(1, len(block.dest_spec)):
                expr = expr + block.dest_spec[i] + in_vars[i]
            block_hp = hp.Assign(var_name=out_var, expr=expr)
        elif block.type in ["or", "and"]:
            if block.type == "or":
                block_hp = hp.Assign(var_name=out_var, expr="max(" + ", ".join(in_vars) + ")")
            elif block.type == "and":
                block_hp = hp.Assign(var_name=out_var, expr="min(" + ", ".join(in_vars) + ")")
        elif block.type == "relation":
            block_hp = hp.Assign(var_name=out_var, expr=block.relation.join(in_vars))
        elif block.type == "switch":
            cond0 = in_vars[1] + block.relation + block.threshold
            cond_hp0 = hp.Condition(cond=cond0, hp=hp.Assign(var_name=out_var, expr=in_vars[0]))
            cond2 = in_vars[1] + block.neg_relation + block.threshold
            cond_hp2 = hp.Condition(cond=cond2, hp=hp.Assign(var_name=out_var, expr=in_vars[2]))
            block_hp = hp.Sequence(cond_hp0, cond_hp2)
        discrete_hps.append(hp.Condition(cond=cond, hp=block_hp))

    # Get the time process
    # Compute the GCD of sample times of all the discrete blocks
    known_st = []
    unknown_st = []
    for block in blocks:
        if hasattr(block, "st") and re.match("\\d+", block.st):
            known_st.append(int(block.st))
        elif hasattr(block, "st"):
            unknown_st.append(block.name)
    if known_st:
        st_gcd = reduce(gcd, known_st) if len(known_st) >= 2 else known_st[0]
        unknown_st.append(str(st_gcd))
    if len(unknown_st) == 1:
        st_gcd = unknown_st[0]  # str(st_gcd)
    else:  # len(unknown_st) >= 2
        st_gcd = "gcd(" + ", ".join(unknown_st) + ")"
    temp = hp.Assign(var_name="temp", expr="t")
    time_ode = hp.ODE(eqs=[("t", "1")], constraint="t<temp+" + st_gcd)
    time_process = hp.Sequence(temp, time_ode)

    # Get loop body
    loop_hps = in_channels + discrete_hps + out_channels
    loop_hps.append(time_process)
    loop_hps = hp.Sequence(*loop_hps)

    process = hp.Sequence(init_hp, hp.Loop(loop_hps))
    # process.name = "PD" + str(process_num)
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
        blocks_dict[block.name] = block
