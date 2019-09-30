from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import *
from ss2hcsp.sl.sl_diagram import get_gcd
from itertools import product


def translate_continuous(diagram):
    # Get block dictionary
    block_dict = {block.name: block for block in diagram["diag"]}
    # Get input and output channels
    in_channels = [hp.InputChannel(ch_name="ch_" + var_name + bran_num, var_name=var_name)
                   for var_name, bran_num in sorted(diagram["in"])]
    out_channels = [hp.OutputChannel(ch_name="ch_" + expr + bran_num, expr=AVar(expr))
                    for expr, bran_num in sorted(diagram["out"])]

    # Get initial processes and ODEs
    init_hps = []
    ode_eqs = []
    for block in block_dict.values():
        if block.type == "integrator":
            out_vars = block.get_output_vars()
            assert isinstance(out_vars, set) and len(out_vars) == 1
            out_var = out_vars.pop()
            init_hps.append(hp.Assign(out_var, AConst(block.init_value)))
            in_vars = block.get_input_vars()
            assert isinstance(in_vars, set) and len(in_vars) == 1
            in_var = in_vars.pop()
            ode_eqs.append((out_var, AVar(in_var)))
        elif block.type == "unit_delay":
            out_vars = block.get_output_vars()
            assert isinstance(out_vars, set) and len(out_vars) == 1
            out_var = out_vars.pop()
            ode_eqs.append((out_var, AConst(0)))
    assert init_hps
    init_hp = init_hps[0] if len(init_hps) == 1 else hp.Sequence(*init_hps)

    # Delete integrator blocks
    integator_names = [name for name, block in block_dict.items() if block.type == "integrator"]
    for name in integator_names:
        del block_dict[name]

    # Constant blocks are for substitution
    var_substitute = Conditional_Inst()  # an object for variable substitution
    for block in block_dict.values():
        if block.type == "constant":
            out_var, cond_inst = block.get_var_map()
            var_substitute.add(out_var, cond_inst)
    # Delete constant blocks
    constant_names = [name for name, block in block_dict.items() if block.type == "constant"]
    for name in constant_names:
        del block_dict[name]

    # Variable substitution
    while block_dict:
        block_pool = dict()
        for name, block in block_dict.items():
            src_blocks = block.get_src_blocks()
            assert isinstance(src_blocks, set)
            if src_blocks.isdisjoint(set(block_dict.keys())):
                assert name not in block_pool
                block_pool[name] = block
        assert block_pool
        for block in block_pool.values():
            assert len(block.get_var_map()) == 1  # for current version
            for out_var, cond_inst in block.get_var_map().items():
                var_substitute.add(out_var, cond_inst)
        # Delete blocks in block_pool from block_dict
        for name in block_pool.keys():
            del block_dict[name]

    # Delete useless variables from var_substitute
    useful_vars = [in_var.name for _, in_var in ode_eqs]  # in_vars of ODEs are useful
    # Expressions (variables) on output channels are useful
    useful_vars.extend(out_ch.expr.name for out_ch in out_channels)
    useless_vars = set(var_substitute.data.keys()) - set(useful_vars)
    for var in useless_vars:
        del var_substitute.data[var]

    # Get composite condition (evolution domain for ODEs) from var_substitute
    var_list = list(var_substitute.data.keys())
    cond_inst_list = list(var_substitute.data.values())
    assert all(var_substitute.data[var_list[i]] == cond_inst_list[i] for i in range(len(var_substitute.data)))
    cond_to_var_to_expr = dict()  # var can be substituted by expr if cond is saftisfied
    for composition in product(*cond_inst_list):
        # composition is in form of [(cond0, expr0), ..., (condn, exprn)]
        conditions = set(cond for cond, _ in composition)
        if var_substitute.conflicting(conditions):
            continue
        comp_cond = conj(*conditions)  # composite condition
        assert comp_cond not in cond_to_var_to_expr
        cond_to_var_to_expr[comp_cond] = dict()
        assert len(var_list) == len(composition)
        for var, (_, expr) in zip(var_list, composition):
            cond_to_var_to_expr[comp_cond][var] = expr

    # Get ODEs by cond_to_var_expr
    ode_hps = []
    for cond, var_to_expr in cond_to_var_to_expr.items():
        # Update ode_eqs by var_to_expr
        new_ode_eqs = []
        for out_var, in_var in ode_eqs:
            assert isinstance(out_var, str) and isinstance(in_var, AVar)
            if in_var.name in var_to_expr:
                in_var = var_to_expr[in_var.name]
                assert isinstance(in_var, AExpr)
            new_ode_eqs.append((out_var, in_var))
        # Update expressions on output channels by var_to_expr
        new_out_channels = []
        for out_ch in out_channels:
            assert isinstance(out_ch.expr, AVar)
            if out_ch.expr.name in var_to_expr:
                new_expr = var_to_expr[out_ch.expr.name]
                assert isinstance(new_expr, AExpr)
                new_out_channels.append(hp.OutputChannel(ch_name=out_ch.ch_name, expr=new_expr))
            else:
                new_out_channels.append(hp.OutputChannel(ch_name=out_ch.ch_name, expr=out_ch.expr))
        io_comms = [(io_ch, hp.Skip()) for io_ch in in_channels + new_out_channels]
        ode_hps.append(hp.ODE_Comm(eqs=new_ode_eqs, constraint=cond, io_comms=io_comms))

    assert ode_hps
    result_hp = hp.Sequence(init_hp, hp.Loop(ode_hps[0])) if len(ode_hps) == 1 \
        else hp.Sequence(init_hp, hp.Loop(hp.Sequence(*ode_hps)))
    return result_hp


def translate_discrete(diagram):
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


def get_hcsp(dis_subdiag_with_chs, con_subdiag_with_chs):
    """Compute the discrete and continuous processes from a diagram,
    which is represented as discrete and continuous subdiagrams."""
    processes = hp.HCSPProcess()
    main_processes = []
    # Compute the discrete processes from discrete subdiagrams
    num = 0
    for diag in dis_subdiag_with_chs:
        name = "PD" + str(num)
        # discrete_process = translate_discrete(diag)
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

