"""Translation from diagrams to HCSP processes."""

from decimal import Decimal

from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AConst, AVar, OpExpr, RelExpr, true_expr, subst_all, conj, neg_expr, ListExpr
from ss2hcsp.sl.sl_block import get_gcd
from ss2hcsp.hcsp.module import HCSPModule
from ss2hcsp.hcsp import hcsp
from ss2hcsp.sf import sf_convert
from ss2hcsp.hcsp.optimize import full_optimize_module
from ss2hcsp.sl.sl_diagram import SL_Diagram


def translate_discrete(diagram, chart_parameters):
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


def translate_continuous(diagram):
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
                          'sqrt', 'switch', 'sine', 'fcn', 'mux', 'selector', 'saturation'):
            var_subst.update(block.get_var_subst())
        elif block.type == "integrator":
            in_var = block.dest_lines[0].name
            out_var = block.src_lines[0][0].name
            init_hps.append(hp.Assign(out_var, AConst(block.init_value)))
            equations.append((out_var, AVar(in_var)))
            if block.enable != true_expr:
                constraints.append(block.enable)
        elif block.type == "transfer_fcn":
            in_var = block.dest_lines[0].name
            out_var = block.src_lines[0][0].name
            init_hps.append(hp.Assign(out_var, AConst(0)))
            coeff = AConst(block.get_coeff())
            equations.append((out_var, OpExpr("-", OpExpr("*", coeff, AVar(in_var)), OpExpr("*", coeff, AVar(out_var)))))
            if block.enable != true_expr:
                constraints.append(block.enable)
        elif block.type == "triggered_subsystem":
            init_hps.extend(block.get_init_hps())
            init_hps.append(hp.Assign(block.triggered, AConst(0)))
            trig_cond = block.get_continuous_triggered_condition()
            trig_procs.append((trig_cond, hp.Var(block.name)))
            constraints.append(neg_expr(trig_cond))
            procedures.extend(block.get_procedures())
        elif block.type in ('scope', 'in_port', 'out_port'):  # ignore
            pass
        else:
            raise NotImplementedError('Unrecognized continuous block: %s' % block.type)

    # Perform some pre-processing: first substitute the lists
    for name, e in var_subst.items():
        if isinstance(e, ListExpr):
            for name2, e2 in var_subst.items():
                var_subst[name2] = e2.subst({name: e}).simplify()

    for i in range(len(equations)):
        var, e = equations[i]
        equations[i] = (var, subst_all(e, var_subst))

    return init_hps, equations, var_subst, constraints, trig_procs, procedures


def get_hcsp(diagram: SL_Diagram):
    dis_init_hps, dis_procedures, output_hps, update_hps, sample_time = \
        translate_discrete(diagram.discrete_blocks, diagram.chart_parameters)
    con_init_hps, equations, var_subst, constraints, trig_procs, con_procedures = \
        translate_continuous(diagram.continuous_blocks)

    # Initialization
    init_hps = [hp.Assign("t", AConst(0)), hp.Assign("_tick", AConst(0))] + dis_init_hps + con_init_hps
    for constant, val in diagram.constants.items():
        init_hps.append(hp.Assign(constant, AConst(val)))
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
    procedures = [hp.Procedure(name=proc_name, hp=proc_hp) for proc_name, proc_hp in dict_procs.items()]

    # Get outputs
    outputs = []
    for scope in diagram.scopes:
        in_vars = [line.name for line in scope.dest_lines]
        for in_var in in_vars:
            subst_e = hp.subst_all(AVar(in_var), var_subst)
            if subst_e == AVar(in_var):
                outputs.append(hp.HCSPOutput(in_var))
            else:
                outputs.append(hp.HCSPOutput(in_var, subst_e))
    return HCSPModule(name="P", code=main_hp, procedures=procedures, outputs=outputs)


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
        diagram.connect_goto()
        diagram.separate_diagram()

        # Convert to HCSP
        result_hp = get_hcsp(diagram)

        # Optimize module
        hp = result_hp.code
        procs = dict((proc.name, proc.hp) for proc in result_hp.procedures)
        procs, hp = full_optimize_module(procs, hp)
        result_hp.procedures = [hcsp.Procedure(name, hp) for name, hp in procs.items()]
        result_hp.code = hp

        print(result_hp.export())
