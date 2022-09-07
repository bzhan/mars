"""Translation from diagrams to HCSP processes."""
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import *
from ss2hcsp.sl.sl_block import SL_Block, get_gcd
from ss2hcsp.sl.Continuous.signalBuilder import SignalBuilder
from itertools import product
import operator
from ss2hcsp.hcsp.parser import expr_parser, hp_parser
from ss2hcsp.sl.mux.mux import Mux
from ss2hcsp.hcsp.module import HCSPModule
from ss2hcsp.hcsp import hcsp
from ss2hcsp.sf import sf_convert
from ss2hcsp.hcsp.optimize import full_optimize_module
from ss2hcsp.sl.sl_diagram import SL_Diagram


def translate_continuous(diagram):
    # Get block dictionary
    block_dict = {block.name: block for block in diagram}
    # Get input and output channels
    in_channels, out_channels = [], []
    for block in block_dict.values():
        for line in block.dest_lines:
            if line.src not in block_dict:
                in_channels.append(hp.InputChannel(ch_name=line.ch_name, var_name=line.name))
        for lines in block.src_lines:
            for line in lines:
                if line.dest not in block_dict:
                    out_channels.append(hp.OutputChannel(ch_name=line.ch_name, expr=AVar(line.name)))
    in_channels.sort(key=operator.attrgetter("ch_name"))
    out_channels.sort(key=operator.attrgetter("ch_name"))

    # Get initial process and ODEs
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
        # elif block.type == "unit_delay":
        #     out_vars = block.get_output_vars()
        #     assert isinstance(out_vars, set) and len(out_vars) == 1
        #     out_var = out_vars.pop()
        #     ode_eqs.append((out_var, AConst(0)))
    # Delete integrator blocks
    integator_names = [name for name, block in block_dict.items() if block.type == "integrator"]
    for name in integator_names:
        del block_dict[name]

    # Constant blocks are for substitution
    var_substitute = Conditional_Inst()  # an object for variable substitution
    for block in block_dict.values():
        if block.type == "constant":
            var_map = block.get_var_map()
            assert len(var_map) == 1
            out_var, cond_inst = var_map.popitem()
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
                assert isinstance(in_var, Expr)
            new_ode_eqs.append((out_var, in_var))
        # Update expressions on output channels by var_to_expr
        new_out_channels = []
        for out_ch in out_channels:
            assert isinstance(out_ch.expr, AVar)
            if out_ch.expr.name in var_to_expr:
                new_expr = var_to_expr[out_ch.expr.name]
                assert isinstance(new_expr, Expr)
                new_out_channels.append(hp.OutputChannel(ch_name=out_ch.ch_name, expr=new_expr))
            else:
                new_out_channels.append(hp.OutputChannel(ch_name=out_ch.ch_name, expr=out_ch.expr))
        io_comms = [(io_ch, hp.Skip()) for io_ch in in_channels + new_out_channels]
        if io_comms:
            ode_hps.append(hp.ODE_Comm(eqs=new_ode_eqs, constraint=cond, io_comms=io_comms))
        else:
            ode_hps.append(hp.ODE(eqs=new_ode_eqs, constraint=cond))

    # # Initialise input variables (Xiong: It seems not necessary, because initially,
    # # input variables should receive initial values along input channels
    # # from the environment (discrete processes) )
    # initialised_vars = [init_hp.var_name for init_hp in init_hps]
    # assert len(initialised_vars) == len(set(initialised_vars))  # no repeated initialised varaibles
    # # Xiong: Initially, the continous process should send the initial values of all output variables,
    # # and then receive the intial values of all input variables.
    out_comms = []
    in_comms = []
    for ode_hp in ode_hps:
        if isinstance(ode_hp, hp.ODE_Comm):
            for io_comm in ode_hp.io_comms:
                if isinstance(io_comm[0], hp.OutputChannel):
                    out_comms.append((io_comm[0], hp_parser.parse("num := num - 1;")))
                elif isinstance(io_comm[0], hp.InputChannel):
                    in_comms.append((io_comm[0], hp_parser.parse("num := num - 1;")))
                else:
                    raise RuntimeError("It must be a channel operation!")

    send_out_vars = hp.Skip()  # no output channel operations
    if len(out_comms) == 1:
        send_out_vars = out_comms[0][0]
    elif len(out_comms) >= 2:
        send_out_vars = hp.Sequence(hp_parser.parse("num := %s;" % len(out_comms)),
                                    hp.Loop(hp=hp.SelectComm(*out_comms), constraint=expr_parser.parse("num > 0")))

    receive_in_vars = hp.Skip()  # no input channel operations
    if len(in_comms) == 1:
        receive_in_vars = in_comms[0][0]
    elif len(in_comms) >= 2:
        receive_in_vars = hp.Sequence(hp_parser.parse("num := %s;" % len(in_comms)),
                                      hp.Loop(hp=hp.SelectComm(*in_comms), constraint=expr_parser.parse("num > 0")))

    init_hps.extend([send_out_vars, receive_in_vars])

    # ch_hp = io_comm[0]
    # if isinstance(ch_hp, hp.InputChannel):
    #     var_name = ch_hp.var_name
    #     if var_name not in initialised_vars:
    #         # updated by lqq
    #         init_hps.append(hp.Assign(var_name, AConst(1)))
    #         initialised_vars.append(var_name)
    assert init_hps
    init_ode = hp.Sequence(*init_hps)

    assert ode_hps
    # cond_ode_hps = []
    # for ode_hp in ode_hps:
    #     assert isinstance(ode_hp, (hp.ODE, hp.ODE_Comm))
    #     if ode_hp.constraint == true_expr:
    #         cond_ode_hps.append(ode_hp)
    #     else:
    #         cond_ode_hps.append(hp.Condition(cond=ode_hp.constraint, hp=ode_hp))
    # result_hp = hp.Sequence(init_ode, hp.Loop(cond_ode_hps[0])) if len(cond_ode_hps) == 1 \
    #     else hp.Sequence(init_ode, hp.Loop(hp.Sequence(*cond_ode_hps)))
    result_hp = hp.Sequence(init_ode, hp.Loop(ode_hps[0])) if len(ode_hps) == 1\
        else hp.Sequence(init_ode, hp.Loop(hp.Sequence(*ode_hps)))
    return result_hp


def translate_discrete(diagram):
    def get_block_hp(_block):  # Get the hcsp of a block from its var_map
        if _block.type == "unit_delay":
            _in_var = _block.dest_lines[0].name
            _out_var = _block.src_lines[0][0].name
            delay_out_var = "delay_" + _out_var
            return hp.Sequence(hp.Assign(_out_var, AVar(delay_out_var)),
                               hp.Assign(delay_out_var, AVar(_in_var)))

        _var_map = _block.get_var_map()
        processes = []
        for _out_var, cond_expr_list in _var_map.items():
            assert all(isinstance(_cond, Expr) and isinstance(_expr, (Expr, Expr))
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

    # Topological sorting for blocks in the discrete subdiagram
    def topo_sort():
        while block_dict:
            block_pool = dict()
            for name, block in block_dict.items():
                src_blocks = block.get_src_blocks()
                assert isinstance(src_blocks, set)
                if src_blocks.isdisjoint(set(block_dict.keys())):
                    assert name not in block_pool
                    block_pool[name] = block
            if not block_pool:
                break_loop()
                break
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
                st_to_hps[block.st].append(get_block_hp(block))
                # Get the input channels of the block
                for line in block.dest_lines:
                    if line.src not in all_blocks:
                        st_to_in_chs[block.st].append(hp.InputChannel(ch_name=line.ch_name, var_name=line.name))
                st_to_in_chs[block.st].sort(key=operator.attrgetter("ch_name"))
                for lines in block.src_lines:
                    for line in lines:
                        if line.dest not in all_blocks:
                            st_to_out_chs[block.st].append(hp.OutputChannel(ch_name=line.ch_name, expr=AVar(line.name)))
                st_to_out_chs[block.st].sort(key=operator.attrgetter("ch_name"))
            # Get each process wrt. Sample Time
            for st in st_to_hps.keys():
                # The condition of time is in form of t%st == 0
                cond_time = RelExpr("==", OpExpr("%", AVar("t"), AConst(st)), AConst(0))
                # The process is in form of in_chs?;hcsp;out_chs!
                assert st_to_hps[st]
                st_processes = st_to_in_chs[st] + st_to_hps[st] + st_to_out_chs[st]
                st_process = st_processes[0] if len(st_processes) == 1 else hp.Sequence(*st_processes)
                main_processes.append(hp.Condition(cond_time, st_process))
            # Delete blocks in block_pool from block_dict
            for name in block_pool.keys():
                del block_dict[name]

    # Break the loop in the remaining diagram
    # At present, we assume the loop is caused by unit_delay blocks
    def break_loop():
        # Find a head: the block whose source blocks in the current diagram are all unit_delay blocks
        head_block = SL_Block()
        for name, block in block_dict.items():
            src_blocks = block.get_src_blocks()
            assert isinstance(src_blocks, set)
            if all(block_dict[src_block].type == "unit_delay"
                   for src_block in src_blocks & set(block_dict.keys())):
                head_block = block
                break

        # Translate the head block
        # First, get all the input channels of the head block
        in_chs_head = []
        for line in head_block.dest_lines:
            # The head block can only read the delayed (old) value of the unit_delay blocks
            if line.src in block_dict:
                assert block_dict[line.src].type == "unit_delay"
                line.name = "delay_" + line.name
            elif line.src not in all_blocks:
                in_chs_head.append(hp.InputChannel(ch_name=line.ch_name, var_name=line.name))
        in_chs_head.sort(key=operator.attrgetter("ch_name"))
        # Then, get all the output channels of the head block
        out_chs_head = []
        for lines in head_block.src_lines:
            for line in lines:
                if line.dest not in all_blocks:
                    out_chs_head.append(hp.OutputChannel(ch_name=line.ch_name, expr=AVar(line.name)))
        out_chs_head.sort(key=operator.attrgetter("ch_name"))
        # Finally, get the HCSP process of the head block
        head_processes = in_chs_head + [get_block_hp(head_block)] + out_chs_head
        # After translation, the names of the dest_lines of the head block should be changed back
        for line in head_block.dest_lines:
            if line.name.startswith("delay_"):
                line.name = line.name[6:]
        head_process = head_processes[0] if len(head_processes) == 1 else hp.Sequence(*head_processes)
        cond_time = RelExpr("==", OpExpr("%", AVar("t"), AConst(head_block.st)), AConst(0))
        main_processes.append(hp.Condition(cond_time, head_process))

        # Delete the head block from the loop
        del block_dict[head_block.name]

        # Continue the topological sorting after deleting the head block from the loop
        topo_sort()

    # Get block dictionary
    block_dict = {block.name: block for block in diagram}
    all_blocks = list(block_dict.keys())

    # The case that there are only constant blocks in block_dict
    # if all(block.type == "constant" for block in block_dict.values()):
    #     assert len(block_dict) == 1
    #     _, block = block_dict.popitem()
    #     line = block.src_lines[0][0]
    #     return hp.Condition(cond=RelExpr("==", ModExpr(AVar("t"), AConst(block.st)), AConst(0)),
    #                         hp=hp.OutputChannel(ch_name=line.ch_name, expr=AConst(block.value)))

    # Get initial processes
    init_hp = hp.Assign("t", AConst(0))
    for block in block_dict.values():
        if block.type == "constant":
            var_map = block.get_var_map()
            assert len(var_map) == 1
            (out_var, [(_, expr)]) = var_map.popitem()
            assert isinstance(expr, AConst)
            init_hp = hp.Sequence(init_hp, hp.Assign(out_var, expr))
        elif block.type == "unit_delay":
            init_hp = hp.Sequence(init_hp,
                                  hp.Assign("delay_"+block.src_lines[0][0].name,
                                            hp.AConst(block.init_value)))

    # Delete Constant blocks
    constant_block_names = [name for name, block in block_dict.items() if block.type == "constant"]
    for name in constant_block_names:
        del block_dict[name]

    # Get diagram sample time and the wait process
    diagram_st = get_gcd([block.st for block in block_dict.values()]) if len(block_dict) >0 else 1
    wait_st = hp.Sequence(hp.Wait(AConst(diagram_st)),
                          hp.Assign("t", OpExpr("+", AVar("t"), AConst(diagram_st))))

    # Get main processes
    main_processes = []
    topo_sort()

    # Get loop body of the result process
    main_processes.append(wait_st)
    result_hp = hp.Sequence(init_hp, hp.Loop(hp.Sequence(*main_processes)))
    return result_hp


def new_translate_discrete(diagram, chart_parameters):
    """Obtain procedures for the discrete part of the diagram."""
    assert isinstance(diagram, list)  # diagram is a list of blocks
    sample_time = get_gcd([block.st for block in diagram
                          if isinstance(block.st, (int, Decimal)) and block.st > 0])
    block_dict = {block.name: block for block in diagram}

    # Record initializations
    init_hps = list()

    # Storing procedures generated when translating
    procedures = list()

    # Delete in_ and out_ports from block_dict
    port_names = [name for name, block in block_dict.items() if block.type in ("in_port", "out_port")]
    for port_name in port_names:
        del block_dict[port_name]

    # Translate Stateflow charts
    charts = [block for block in block_dict.values() if block.type == "stateflow"]

    # First, for the charts triggered by function calls, obtain mapping
    # from events to corresponding charts.
    fun_call_map = dict()
    for chart in charts:
        for trigger_type, event in chart.input_events:
            if trigger_type == 'function-call':
                fun_call_map[event] = chart.name
    for chart in charts:
        converter = sf_convert.SFConvert(
            chart, chart_parameters=chart_parameters[chart.name], translate_io=False,
            fun_call_map=fun_call_map)
        init_hps.append(hcsp.Var(converter.init_name(chart.name)))
        chart.exec_name = converter.exec_name(charts[0].name)
        _procedures = converter.get_procs()
        for _name, _hp in _procedures.items():
            procedures.append(hcsp.Procedure(_name, _hp))

    # Generate init_hp
    for block in block_dict.values():
        if block.type == "constant":
            out_var = block.src_lines[0][0].name
            init_hps.append(hp.Assign(var_name=out_var, expr=AConst(block.value)))
        elif block.type == "unit_delay":
            init_hps.append(hp.Assign(var_name=block.name+"_state", expr=AConst(block.init_value)))
        elif block.type == "discrete_PID_controller":
            init_hps.extend(block.get_init_hps())
        elif block.type == "triggered_subsystem":
            init_hps.extend(block.get_init_hps())
            procedures.extend(block.get_procedures())
        elif block.type == "signalBuilder":
            init_hps.append(block.get_init_hp())
        elif block.type == "stateflow":
            init_hps.extend(block.get_init_hps())
        elif block.type == "DiscretePulseGenerator":
            init_hps.append(block.get_init_hp())

    # Delete Constant blocks
    block_names = [name for name, block in block_dict.items() if block.type == "constant"]
    for name in block_names:
        del block_dict[name]

    # Get a topological sort of the blocks
    # First, move all the Unit_Delay blocks from block_dict to sorted_blocks
    sorted_blocks = [block for block in block_dict.values() if block.type == "unit_delay"]
    for block in sorted_blocks:
        del block_dict[block.name]

    # Get a topological sort of the remaining blocks
    while block_dict:
        head_block_names = []
        for name, block in block_dict.items():
            src_blocks = block.get_src_blocks()
            if src_blocks.isdisjoint(set(block_dict.keys())):
                sorted_blocks.append(block)
                head_block_names.append(name)
        assert head_block_names
        for name in head_block_names:
            del block_dict[name]

    # Get the OUTPUT of each block in sorted_blocks
    output_hps = []
    update_hps = []
    for block in sorted_blocks:
        if block.st == sample_time:
            # Block runs at every sample time
            output_hps.append(block.get_output_hp())
        elif block.st < 0:
            # Block may be triggered, add the triggering code
            output_hps.append(block.get_output_hp())
        else:
            assert block.st % sample_time == 0
            period = block.st // sample_time
            output_hps.append(hp.ITE([(
                RelExpr("==", OpExpr("%", AVar("_tick"), AConst(period)), AConst(0)),
                block.get_output_hp())]))

        if block.type == "unit_delay":
            if block.st == sample_time:
                update_hps.append(block.get_update_hp())
            else:
                assert block.st % sample_time == 0
                period = block.st // sample_time
                update_hps.append(hp.ITE([(
                    RelExpr("==", OpExpr("%", AVar("_tick"), AConst(period)), AConst(0)),
                    block.get_update_hp())]))
    return init_hps, procedures, output_hps, update_hps, sample_time


def new_translate_continuous(diagram):
    """Translate continuous diagram.

    diagram : SL_Diagram

    Returns five-tuple:
    init_hps: initialization processes.
    equations: equations of the ODE.
    constraints: constraint of the ODE.
    trig_procs: triggered procedures.
    procedures: list of procedures from triggered subsystems.

    """
    # tt is the LOCAL evolution time of continuous process
    init_hps = [hp.Assign(var_name="tt", expr=AConst(0))]
    equations = [("tt", AConst(1))]  # tt_dot = 1
    constraints = []
    trig_procs = []
    procedures = []

    # Dictionary of variable substitutions. There should be no loops
    # in substitution.
    var_subst = dict()

    for block in diagram:
        if block.type in ('add', 'product', 'bias', 'gain', 'constant', 'square',
                          'sqrt', 'switch', 'sine'):
            var_subst.update(block.get_var_subst())
        elif block.type == "integrator":
            in_var = block.dest_lines[0].name
            out_var = block.src_lines[0][0].name
            init_hps.append(hp.Assign(out_var, AConst(block.init_value)))
            equations.append((out_var, AVar(in_var)))
            if block.enable != true_expr:
                constraints.append(block.enable)
        elif block.type == "triggered_subsystem":
            init_hps.extend(block.get_init_hps())
            init_hps.append(hp.Assign(block.triggered, AConst(0)))
            trig_cond = block.get_continuous_triggered_condition()
            trig_procs.append((trig_cond, hp.Var(block.name)))
            constraints.append(neg_expr(trig_cond))
            procedures.extend(block.get_procedures())
        elif block.type in ('scope in_port out_port'):  # ignore
            pass
        else:
            raise NotImplementedError('Unrecognized continuous block: %s' % block.type)

    for i in range(len(equations)):
        var, e = equations[i]
        equations[i] = (var, subst_all(e, var_subst))

    return init_hps, equations, var_subst, constraints, trig_procs, procedures


def new_get_hcsp(discrete_diagram, continuous_diagram, chart_parameters, outputs=()):
    dis_init_hps, dis_procedures, output_hps, update_hps, sample_time = \
        new_translate_discrete(discrete_diagram, chart_parameters)
    con_init_hps, equations, var_subst, constraints, trig_procs, con_procedures = \
        new_translate_continuous(continuous_diagram)

    # Initialization
    init_hps = [hp.Assign("t", AConst(0)), hp.Assign("_tick", AConst(0))] + dis_init_hps + con_init_hps
    init_hp = init_hps[0] if len(init_hps) == 1 else hp.Sequence(*init_hps)

    ### Discrete process ###
    discrete_hps = output_hps + update_hps
    discrete_hp = hp.seq(discrete_hps)
    discrete_hp = hp.subst_comm_all(discrete_hp, var_subst)

    ### Continuous process ###

    # If sample_time = 0, the entire diagram is continuous. Arbitrarily
    # choose 1 as sample time
    if sample_time == 0:
        sample_time = 1

    # Add tt < sample_time to the constraint
    time_constraint = RelExpr("<", AVar("tt"), AConst(sample_time))
    constraints.append(time_constraint)

    # Form ODE
    continuous_hp = hp.ODE(eqs=equations, constraint=conj(*constraints))
    names_triggered = None
    if trig_procs:
        names_triggered = list()
        for _, sys_name in trig_procs:
            name_triggered = sys_name.name + "_triggered"
            names_triggered.append(
                hp.ITE([(RelExpr(">", AVar(name_triggered), AConst(0)),
                        hp.Assign(var_name=name_triggered,
                                          expr=OpExpr("-", AVar(name_triggered), AConst(1))))]))
        names_triggered = hp.seq(names_triggered)
        trig_proc = list()
        for cond, sys_name in trig_procs:
            set_triggered = hp.ITE(if_hps=[(RelExpr("<", AVar("tt"), AConst(sample_time)),
                                            hp.Assign(var_name=sys_name.name+"_triggered", expr=AConst(1)))],
                                   else_hp=hp.Assign(var_name=sys_name.name+"_triggered", expr=AConst(2))
                                   )
            trig_proc.append(hp.ITE([(cond, hp.Sequence(sys_name, set_triggered))]))
        trig_proc = hp.Sequence(*trig_proc) if len(trig_proc) >= 2 else trig_proc[0]
        continuous_hp = hp.Loop(hp=hp.Sequence(continuous_hp, trig_proc), constraint=time_constraint)

    # Update t := t + tt
    update_t = hp.Assign("t", OpExpr("+", AVar("t"), AVar("tt")))

    # Update tick := tick + 1
    update_tick = hp.Assign("_tick", OpExpr("+", AVar("_tick"), AConst(1)))

    # Reset tt := 0
    reset_tt = hp.Assign(var_name="tt", expr=AConst(0))

    if names_triggered:
        continuous_hp = hp.Sequence(names_triggered, continuous_hp, update_t, update_tick, reset_tt)
    else:
        continuous_hp = hp.Sequence(continuous_hp, update_t, update_tick, reset_tt)

    # Main process
    main_hp = hp.Sequence(init_hp, hp.Loop(hp.Sequence(discrete_hp, continuous_hp)))

    # Get procedures
    procedures = dis_procedures + con_procedures

    dict_procs = {proc.name: proc.hp for proc in procedures}
    # dict_procs, main_hp = full_optimize_module(dict_procs, main_hp)
    procedures = [hp.Procedure(name=proc_name, hp=proc_hp) for proc_name, proc_hp in dict_procs.items()]
    return HCSPModule(name="P", code=main_hp, procedures=procedures, outputs=outputs)


def get_hcsp(dis_subdiag_with_chs, con_subdiag_with_chs, sf_charts, buffers,
             discretePulseGenerator, muxs, dataStoreMemorys, dataStoreReads, clocks, model_name="P"):
    """Obtain HCSP from a list of disjoint diagrams.
    
    The arguments are:
    dis_subdiag_with_chs - list of discrete diagrams
    con_subdiag_with_chs - list of continuous diagrams
    sf_charts - list of Stateflow charts
    unit_delays - list of unit delay blocks
    buffers - list of buffers

    """
    processes = hp.HCSPProcess()
    main_processes = []
    # triggered_process = []
    # Compute the discrete processes from discrete subdiagrams
    num = 0
    for data in dataStoreMemorys:
        name = "DSM" + str(num)
        processes.add(name, data.get_hcsp())
        main_processes.append(hp.Var(name))
        num += 1
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
    num=0
    for block in discretePulseGenerator:
        for line in block.src_lines:
            for branch in line:
                if isinstance(branch.dest_block,Mux):
                    plus_hcsp = block.get_hcsp()
                    name = "DPG" + str(num)
                    processes.add(name, plus_hcsp)
                    main_processes.append(hp.Var(name))
                else:
                    plus_hcsp = block.get_hcsp1()
                    name = "DPG" + str(num)
                    processes.add(name, plus_hcsp)
                    main_processes.append(hp.Var(name))
        num += 1
    num1=0
    for block in muxs:
        name="Mux"+str(num1)
        processes.add(name, block.get_hp())
        main_processes.append(hp.Var(name))
        num1+=1

    # Compute the stateflow processes
    for chart in sf_charts:
        chart.sf_charts = sf_charts

    # Computer the buffer processes
    for buffer in buffers:
        process_name = buffer.name.replace(" ", "_")
        processes.add(process_name, buffer.get_hcsp())
        main_processes.append(hp.Var(process_name))

    # Get main paralell processes
    assert len(main_processes) >= 1 and len(main_processes) == len(processes.hps)
    if len(main_processes) == 1:
        processes.hps = [(model_name, processes.hps[0][1])]
    else:
            main_process = hp.Parallel(*main_processes)
            processes.insert(n=0, name=model_name, hp=main_process)

    return processes


if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Usage: python sf_convert.py filename")
    else:
        filename = sys.argv[1]
        diagram = SL_Diagram(filename)
        diagram.parse_xml()
        diagram.delete_subsystems()
        diagram.add_line_name()
        diagram.comp_inher_st()
        diagram.inherit_to_continuous()
        diagram.separate_diagram()

        # Convert to HCSP
        result_hp = new_get_hcsp(
            diagram.discrete_blocks, diagram.continuous_blocks,
            diagram.chart_parameters, diagram.outputs)

        # Optimize module
        hp = result_hp.code
        procs = dict((proc.name, proc.hp) for proc in result_hp.procedures)
        procs, hp = full_optimize_module(procs, hp)
        result_hp.procedures = [hcsp.Procedure(name, hp) for name, hp in procs.items()]
        result_hp.code = hp

        print(result_hp.export())
