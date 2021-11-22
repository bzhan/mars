"""Translation from SF Chart to Isabelle."""

from ss2hcsp.sf.sf_state import AND_State, Junction, OR_State
from ss2hcsp.matlab import function


def translate_expr(e):
    if e is None:
        # None in condition means true
        return "Bc True"
    elif isinstance(e, function.AConst):
        return "N %s" % e.value
    elif isinstance(e, function.Var):
        return "V ''%s''" % e.name
    elif isinstance(e, function.OpExpr):
        if e.op_name == "+":
            return "Plus (%s) (%s)" % (translate_expr(e.exprs[0]), translate_expr(e.exprs[1]))
        elif e.op_name == "-" and len(e.exprs) == 1 and isinstance(e.exprs[0], function.AConst):
            return "%s" % (-e.exprs[0].value)
        else:
            print(e.op_name)
            raise NotImplementedError
    elif isinstance(e, function.BConst):
        if e.value == True:
            return "Bc True"
        else:
            return "Bc False"
    elif isinstance(e, function.RelExpr):
        if e.op == ">":
            return "(%s) [>] (%s)" % (translate_expr(e.expr1), translate_expr(e.expr2))
        else:
            raise NotImplementedError
    else:
        print(type(e))
        raise NotImplementedError

def translate_action(c, is_tran_act=False):
    if isinstance(c, function.Skip):
        return "SKIP"
    elif isinstance(c, function.Assign):
        return "%s ::= %s" % (c.lname, translate_expr(c.expr))
    elif isinstance(c, function.FunctionCall):
        if c.func_name == "send":
            if is_tran_act:
                return "send1 ''%s'' True" % c.args[0]
            else:
                return "send1 ''%s'' False" % c.args[0]
        else:
            raise NotImplementedError
    else:
        print(type(c))
        raise NotImplementedError

def translate_actions(cs, is_tran_act=False):
    return ";".join(translate_action(c, is_tran_act=is_tran_act) for c in cs)

def translate_event(event):
    if event is None:
        return "S []"
    elif isinstance(event, function.BroadcastEvent):
        return "S %s" % event.name
    else:
        print(type(event))
        raise NotImplementedError

def translate_state_name(ssid, diagram):
    if ssid is None:
        return "ERROR"
    
    state = diagram.all_states[ssid]
    if isinstance(state, (OR_State, AND_State)):
        return "P %s" % state.name
    elif isinstance(state, Junction):
        return "J %s" % state.ssid
    else:
        raise NotImplementedError

def translate_trans(tran, diagram):
    # Obtain source and destination states
    src_str = translate_state_name(tran.src, diagram)
    dst_str = translate_state_name(tran.dst, diagram)

    # Obtain event, condition, condition action and transition action
    label = tran.label
    event_str = translate_event(label.event)
    cond_str = translate_expr(label.cond)
    cond_act_str = translate_action(label.cond_act, is_tran_act=False)
    tran_act_str = translate_action(label.tran_act, is_tran_act=True)

    return "Trans (%s) (%s) (%s) (%s) (%s) (%s)" % \
        (src_str, event_str, cond_str, cond_act_str, tran_act_str, dst_str)

def translate_state(ssid, diagram):
    state = diagram.all_states[ssid]
    if isinstance(state, OR_State):
        en_str = translate_actions(state.en)
        du_str = translate_actions(state.du)
        ex_str = translate_actions(state.ex)

        if state.inner_trans:
            in_str = ", ".join(translate_trans(tran, diagram) for tran in state.inner_trans)
        else:
            in_str = ""
        
        if state.out_trans:
            out_str = ", ".join(translate_trans(tran, diagram) for tran in state.out_trans)
        else:
            out_str = ""

        if not state.children:
            comp_str = "No_Composition"
        else:
            raise NotImplementedError

        return "state [''%s'']\n  (%s)\n  (%s)\n  (%s)\n  [%s]\n  [%s]\n  %s" % \
            (state.name, en_str, du_str, ex_str, in_str, out_str, comp_str)

    else:
        return ""
