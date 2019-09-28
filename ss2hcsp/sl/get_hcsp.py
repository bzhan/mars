from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import *
from ss2hcsp.sl.sl_diagram import get_gcd
from itertools import product


def translate_continuous(diag):
    """Translate a given diagram to an HCSP program."""

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
                elif block.type in ["add", "product"]:  # Multiple inputs, one output
                    assert len(in_vars) == len(block.dest_spec)
                    exprs = [AVar(var) for var in in_vars]
                    if block.type == "add":
                        res_expr = PlusExpr(signs=block.dest_spec, exprs=exprs)
                    elif block.type == "product":
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
                    assert isinstance(block.st, AExpr)
                    cond0 = RelExpr(op="<=", expr1=AVar("t"), expr2=block.st)
                    cond1 = RelExpr(op=">", expr1=AVar("t"), expr2=block.st)
                    cond_inst.add(var_name=out_var,
                                  cond_inst=[(cond0, AConst(block.init_value)),
                                             (cond1, FunExpr(fun_name="delay",
                                                             exprs=[AVar(in_var), block.st]))])
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
            if cond_inst.conflicting(constraints):
                continue  # because cons_pairs contains mutually exclusive constrains
            constraint = conj(*constraints)
        # ode_hps.append(hp.ODE_Comm(eqs=new_ode_eqs, constraint=bexpr_parse(constraint), io_comms=comm_hps))
        ode_hps.append(hp.ODE_Comm(eqs=new_ode_eqs, constraint=constraint, io_comms=comm_hps))

    process = None
    if len(ode_hps) == 1:
        process = hp.Sequence(hp.Sequence(*init_hps), hp.Loop(ode_hps[0]))
    elif len(ode_hps) >= 2:
        process = hp.Sequence(hp.Sequence(*init_hps), hp.Loop(hp.Sequence(*ode_hps)))
    return process


def translate_discrete_diagram(diagram):
    def get_block_hp(_var_map):  # Get the hcsp of a block from its var_map
        processes = []
        for _out_var, cond_expr_list in _var_map.items():
            assert all(isinstance(_cond, BExpr) and isinstance(_expr, (AExpr, BExpr))
                       for _cond, _expr in cond_expr_list) and cond_expr_list
            if len(cond_expr_list) == 1:
                assert cond_expr_list[0][0] == true_expr
                _expr = cond_expr_list[0][1]
                processes.append(hp.Assign(_out_var, _expr))
            elif len(cond_expr_list) >= 2:
                cond_hp_list = [(_cond, hp.Assign(_out_var, _expr)) for _cond, _expr in cond_expr_list]
                if_hps = cond_hp_list[:-1]
                else_hp = cond_hp_list[-1][1]
                processes.append(hp.ITE(if_hps, else_hp))
        assert processes
        if len(processes) == 1:
            return processes[0]
        else:
            return hp.Sequence(*processes)

    # Get block dictionary
    block_dict = {block.name: block for block in diagram["diag"]}
    # Get input and output channels
    in_channels = [hp.InputChannel(ch_name="ch_" + var_name + bran_num, var_name=var_name)
                   for var_name, bran_num in sorted(diagram["in"])]
    out_channels = [hp.OutputChannel(ch_name="ch_" + expr + bran_num, expr=AVar(expr))
                    for expr, bran_num in sorted(diagram["out"])]

    # Get initial processes
    init_hp = hp.Assign("t", AConst(0))
    for block in block_dict.values():
        if block.type == "constant":
            var_map = block.get_var_map()
            assert len(var_map) == 1
            (out_var, [(_, expr)]) = var_map.popitem()
            assert isinstance(expr, AConst)
            init_hp = hp.Sequence(init_hp, hp.Assign(out_var, expr))

    # Delete Constant blocks
    constant_block_names = [name for name, block in block_dict.items() if block.type == "constant"]
    for name in constant_block_names:
        del block_dict[name]

    # Get diagram sample time and the wait process
    diagram_st = get_gcd([block.st for block in block_dict.values()])
    wait_st = hp.Sequence(hp.Wait(AConst(diagram_st)),
                          hp.Assign("t", PlusExpr("++", [AVar("t"), AConst(diagram_st)])))

    # Get main processes
    main_processes = []
    while block_dict:
        block_pool = dict()
        for name, block in block_dict.items():
            src_blocks = block.get_src_blocks()
            assert isinstance(src_blocks, set)
            if src_blocks.isdisjoint(set(block_dict.keys())):
                assert name not in block_pool
                block_pool[name] = block
        assert block_pool
        # Classify blocks in block_pool by Sample Time
        st_to_hps = dict()
        st_to_in_chs = dict()
        st_to_out_chs = dict()
        for block in block_pool.values():
            # Get the hcsp of the block
            if block.st not in st_to_hps:
                assert (block.st not in st_to_in_chs) and (block.st not in st_to_out_chs)
                st_to_hps[block.st] = []
                st_to_in_chs[block.st] = []
                st_to_out_chs[block.st] = []
            st_to_hps[block.st].append(get_block_hp(block.get_var_map()))
            # Get the input channels of the block
            in_vars = block.get_input_vars()
            for in_ch in in_channels:
                if in_ch.var_name in in_vars:
                    st_to_in_chs[block.st].append(in_ch)
            # Get the output channels of the block
            out_vars = block.get_output_vars()
            for out_ch in out_channels:
                if out_ch.expr.name in out_vars:
                    st_to_out_chs[block.st].append(out_ch)
        # Get each process wrt. Sample Time
        for st in st_to_hps.keys():
            # The condition of time is in form of t%st == 0
            cond_time = RelExpr("==", ModExpr(AVar("t"), AConst(st)), AConst(0))
            # The process is in form of in_chs?;hcsp;out_chs!
            assert st_to_hps[st]
            st_processes = st_to_in_chs[st] + st_to_hps[st] + st_to_out_chs[st]
            st_process = st_processes[0] if len(st_processes) == 1 else hp.Sequence(*st_processes)
            main_processes.append(hp.Condition(cond_time, st_process))
        # Delete blocks in block_pool from block_dict
        for name in block_pool.keys():
            del block_dict[name]

    # Get loop body of the result process
    main_processes.append(wait_st)
    result_hp = hp.Sequence(init_hp, hp.Loop(hp.Sequence(*main_processes)))
    return result_hp


def get_processes(dis_subdiag_with_chs, con_subdiag_with_chs):
    """Compute the discrete and continuous processes from a diagram,
    which is represented as discrete and continuous subdiagrams."""
    processes = hp.HCSPProcess()
    main_processes = []
    # Compute the discrete processes from discrete subdiagrams
    num = 0
    for diag in dis_subdiag_with_chs:
        name = "PD" + str(num)
        # discrete_process = translate_discrete(diag)
        discrete_process = translate_discrete_diagram(diag)
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

