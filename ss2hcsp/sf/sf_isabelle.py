"""Translation from SF Chart to Isabelle."""

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.sf.sf_state import AND_State, Junction, OR_State, GraphicalFunction
from ss2hcsp.sf.sf_convert import SFConvert
from ss2hcsp.matlab import function
from ss2hcsp.matlab import convert


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
            return "N (%s)" % (-e.exprs[0].value)
        elif e.op_name == "-":
            return "Minus (%s) (%s)" % (translate_expr(e.exprs[0]), translate_expr(e.exprs[1]))
        elif e.op_name == '*':
            return "Multiply (%s) (%s)" % (translate_expr(e.exprs[0]), translate_expr(e.exprs[1]))
        elif e.op_name == '/':
            return "Divide (%s) (%s)" % (translate_expr(e.exprs[0]), translate_expr(e.exprs[1]))
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
        elif e.op == ">=":
            return "(%s) [>=] (%s)" % (translate_expr(e.expr1), translate_expr(e.expr2))
        elif e.op == "<":
            return "(%s) [<] (%s)" % (translate_expr(e.expr1), translate_expr(e.expr2))
        elif e.op == "<=":
            return "(%s) [<=] (%s)" % (translate_expr(e.expr1), translate_expr(e.expr2))
        elif e.op == "==":
            return "(%s) [==] (%s)" % (translate_expr(e.expr1), translate_expr(e.expr2))
        elif e.op == "!=":
            return "(%s) [!=] (%s)" % (translate_expr(e.expr1), translate_expr(e.expr2))
        else:
            print(e)
            raise NotImplementedError
    elif isinstance(e, function.LogicExpr):
        if e.op_name == '&&':
            return "(%s) && (%s)" % (translate_expr(e.expr1), translate_expr(e.expr2))
        elif e.op_name == '||':
            return "(%s) || (%s)" % (translate_expr(e.expr1), translate_expr(e.expr2))
        elif e.op_name == '~':
            return "Not (%s)" % (translate_expr(e.expr1))
        else:
            raise NotImplementedError
    elif isinstance(e, function.FunExpr):
        ret_str = ''
        str_end = ''
        for expr in e.exprs:
            ret_str += '([[%s, ' %(translate_expr(expr))
            str_end += ']])'
        ret_str += ('No_Expr' + str_end)
        return ret_str
    elif isinstance(e, function.DirectName):
        return "V ''%s''" % str(e).split('.')[0]
    else:
        print(e)
        print(type(e))
        raise NotImplementedError

def translate_action(c, diagram, is_tran_act=False):
    if isinstance(c, function.Skip):
        return "SKIP"
    elif isinstance(c, function.Assign):
        #print(c.expr)
        if isinstance(c.expr, function.FunExpr):
            ret_str = ''
            str_end = ''
            if isinstance(c.lname, function.Var):
                ret_str += '([[V \'\'%s\'\', ' %(str(c.lname))
                str_end += ']])'
            else:
                for arg in c.lname.args:
                    ret_str += '([[V \'\'%s\'\', ' %(arg)
                    str_end += ']])'
            ret_str += 'No_Expr'
            ret_str += (str_end + "::= ")
            procedures = dict()
            for fun in diagram.diagram.funs:
                procedures[fun.name] = fun
            #print(procedures)
            f = "\'\'" + c.expr.fun_name + "\'\'"
            if isinstance(procedures[c.expr.fun_name], function.Function):
                ret_str += "\'\'" + c.expr.fun_name + "\'\'" + '<'
                ret_str += translate_expr(c.expr)
                ret_str += '>'
            elif isinstance(procedures[c.expr.fun_name], GraphicalFunction):
                ret_str += "\'\'" + c.expr.fun_name + "\'\'" + '<<'
                ret_str += translate_expr(c.expr)
                ret_str += '>>'
            return ret_str
        else:
            if str(c.lname).split('.')[-1] == "data":
                vname = str(c.lname).split('.')[0]
            else:
                vname = c.lname
            return "\'\'%s\'\' ::= %s" % (vname, translate_expr(c.expr))
    elif isinstance(c, function.Sequence):
        return "(%s); (%s)" %(translate_action(c.cmd1, diagram, is_tran_act), translate_action(c.cmd2, diagram, is_tran_act))
    elif isinstance(c, function.FunctionCall):
        if c.func_name == "send":
            args = c.args
            if len(args) == 1 and len(str(args[0]).split('.')) == 1:
                if str(c.args[0]).startswith('M'):
                    return "send3 ''%s'' " % c.args[0]
                else:
                    if is_tran_act:
                        return "send1 ''%s'' True" % c.args[0]
                    else:
                        return "send1 ''%s'' False" % c.args[0]
            #The following two conditions are directed send
            elif len(args) == 2:
                event,direct_name=args[0],args[1]
                direct_name = '\'\', \'\''.join(str(direct_name).split('.'))
                if is_tran_act:
                    return "send2 ''%s'' True [''%s''] " % (event,direct_name)
                else:
                    return "send2 ''%s'' False [''%s''] " % (event,direct_name)
            elif len(args) == 1 and len(str(args[0]).split('.')) > 1:
                tmp = args.split('.')
                event = tmp[-1]
                direct_name = '\'\', \'\''.join(tmp[:-1])
                if is_tran_act:
                    return "send2 ''%s'' True [''%s''] " % (event,direct_name)
                else:
                    return "send2 ''%s'' False [''%s''] " % (event,direct_name)
            else:
                raise NotImplementedError
        elif c.func_name == 'fprintf':
            args = list(c.args)
            if len(args) == 1:
                try:
                    return "print1 ''%s'' " % args[0].value
                except:
                    return "print1 ''test'' "
            else:
                del(args[0])
                expr = ""
                for i in range(0, len(args)):
                    expr += "print2 (V ''" + str(args[i]) + "'')"
                    if i != (len(args)-1):
                        expr += "; "
                return expr
    #matlab functions and graphical fucntions
        else:
            procedures = dict()
            for fun in diagram.diagram.funs:
                procedures[fun.name] = fun
            #print(procedures)
            f = "\'\'" + c.func_name + "\'\'"
            if isinstance(procedures[c.func_name], function.Function):
                ret_str = "No_Expr ::= %s<" %(f)
                str_end = ''
                #print(c.args[0])
                if len(c.args) == 1:
                    return "print1 ''%s'' " % c.args[0].value
                else:
                    for para in c.args:
                        ret_str += '([[%s, ' %(translate_expr(para))
                        str_end += ']])'
                    ret_str += ('No_Expr' + str_end)
                    ret_str += '>'
                    return ret_str
            elif isinstance(procedures[c.func_name], GraphicalFunction):
                ret_str = "No_Expr ::= %s<<" %(f)
                str_end = ''
                for para in c.args:
                    ret_str += '([[%s, ' %(translate_expr(para))
                    str_end += ']])'
                ret_str += ('No_Expr' + str_end)
                ret_str += '>>'
                return ret_str
                
            else:
                raise NotImplementedError
    elif isinstance(c, function.RaiseEvent):
        if len(str(c.event).split('.')) == 1:
            if is_tran_act:
                return "send1 ''%s'' True" % c.event
            else:
                return "send1 ''%s'' False" % c.event
        #The following two conditions are directed send
        else:
            tmp = str(c.event).split('.')
            event = tmp[-1]
            for ssid, state in diagram.all_states.items():
                if state.name == tmp[-2]:
                    direct_name = get_state_path(state)
            if is_tran_act:
                return "send2 ''%s'' True %s " % (event,direct_name)
            else:
                return "send2 ''%s'' False %s " % (event,direct_name)
    else:
        print(type(c))
        return "SKIP"
        #raise NotImplementedError

def translate_actions(cs, diagram, is_tran_act=False):
    actions_str = ''
    for i in range(len(cs)):
        actions_str += translate_action(cs[i], diagram, is_tran_act=is_tran_act)
        if i != len(cs) -1 :
            actions_list = list(actions_str)
            actions_list.insert(0,'(')
            actions_str = ''.join(actions_list)
            actions_str += ');'
    return actions_str

def translate_event(event):
    if event is None:
        return "S []"
    elif isinstance(event, function.BroadcastEvent):
        if event.name.startswith('M'):
            return "M \'\'%s\'\'" % event.name
        else:
            return "S [\'\'%s\'\']" % event.name
    elif isinstance(event, function.TemporalEvent):
        temporal_name = event.temp_op.title()
        now_event = str(event.event)
        if now_event == 'sec':
            now_event = 'Sec'
        return "T1 (%s (\'\'%s\'\') (%s))" % (temporal_name, now_event, translate_expr(event.expr))
    else:
        print(type(event))
        raise NotImplementedError

def get_state_path(state):
    if state.name != '':
        path_list = [state.name]
    else:
        path_list = [str(state.ssid)]
    while state.father:
        if state.father.name != '':
            path_list.append(state.father.name)
        else:
            path_list.append(str(state.father.ssid))
        state = state.father
    path = '['
    for i in range(len(path_list)-2, -1, -1):
        path += ('\'\'' + path_list[i] + '\'\'')
        if i != 0:
            path += ', '
    path += ']'
    return path

def translate_state_name(ssid, diagram, is_GraphicalJunction = False):
    if is_GraphicalJunction:
        if ssid is None:
            return "NONE"
        else:
            return "J [\'\'%s\'\']" %(str(ssid))
    if ssid is None:
        return "NONE"
    
    state = diagram.all_states[ssid]
    path = get_state_path(state)
    #print(type(state))
    #print(state_path)
    if isinstance(state, (OR_State, AND_State)):
        return "P %s" % path
    elif isinstance(state, Junction):
        return "J %s" % path
    else:
        raise NotImplementedError

def translate_trans(tran, diagram, is_GraphicalJunction = False):
    # Obtain source and destination states
    src_str = translate_state_name(tran.src, diagram, is_GraphicalJunction=is_GraphicalJunction)
    dst_str = translate_state_name(tran.dst, diagram, is_GraphicalJunction=is_GraphicalJunction)

    # Obtain event, condition, condition action and transition action
    label = tran.label
    event_str = translate_event(label.event)
    cond_str = translate_expr(label.cond)
    if isinstance(label.cond, function.RelExpr) and isinstance(label.cond.expr1, function.FunExpr):
        cond_str = "(V '''') " + cond_str.split(') ')[1]

    #print(label.tran_act)
    cond_act_str = translate_action(label.cond_act, is_tran_act=False, diagram=diagram)
    tran_act_str = translate_action(label.tran_act, is_tran_act=True, diagram=diagram)

    return "Trans (%s) (%s) (%s) (%s) (%s) (%s)" % \
        (src_str, event_str, cond_str, cond_act_str, tran_act_str, dst_str)

def translate_state(ssid, diagram):
    state = diagram.all_states[ssid]
    if isinstance(state, OR_State):
        en_str = translate_actions(state.en, diagram, is_tran_act=False)
        if en_str == '':
            en_str = 'SKIP'
        du_str = translate_actions(state.du, diagram, is_tran_act=False)
        if du_str == '':
            du_str = 'SKIP'
        ex_str = translate_actions(state.ex, diagram, is_tran_act=False)
        if ex_str == '':
            ex_str = 'SKIP'

        state_path = get_state_path(state)

        if state.inner_trans:
            in_str = ", ".join(translate_trans(tran, diagram) for tran in state.inner_trans)
        else:
            in_str = ""
        
        if state.out_trans:
            out_str = ", ".join(translate_trans(tran, diagram) for tran in state.out_trans)
        else:
            out_str = ""
        for tran in state.out_trans:
            label = tran.label
            tmp_str = ""
            if isinstance(label.cond, function.RelExpr) and isinstance(label.cond.expr1, function.FunExpr):
                procedures = dict()
                for fun in diagram.diagram.funs:
                    procedures[fun.name] = fun
                #print(procedures)
                c = label.cond.expr1
                f = "\'\'" + c.fun_name + "\'\'"
                tmp_str = "((([[V '''', No_Expr]])::="
                if isinstance(procedures[c.fun_name], function.Function):
                    tmp_str += "\'\'" + c.fun_name + "\'\'" + '<'
                    tmp_str += translate_expr(c)
                    tmp_str += '>))'
                elif isinstance(procedures[c.fun_name], GraphicalFunction):
                    tmp_str += "\'\'" + c.fun_name + "\'\'" + '<<'
                    tmp_str += translate_expr(c)
                    tmp_str += '>>))'
                en_list = list(en_str)
                en_list.insert(0,'(')
                en_str = "".join(en_list)
                en_str += "); "
                en_str += tmp_str

        if not state.children:
            comp_str = "No_Composition"
        else:
            comp_str = translate_composition(ssid, diagram)
            if comp_str == '':
                comp_str = "No_Composition"

        return "State %s\n  (%s)\n  (%s)\n  (%s)\n  [%s]\n  [%s]\n  (%s)" % \
            (state_path, en_str, du_str, ex_str, in_str, out_str, comp_str)
    elif isinstance(state, AND_State):
        en_str = translate_actions(state.en, diagram, is_tran_act=False)
        if en_str == '':
            en_str = 'SKIP'
        du_str = translate_actions(state.du, diagram, is_tran_act=False)
        if du_str == '':
            du_str = 'SKIP'
        ex_str = translate_actions(state.ex, diagram, is_tran_act=False)
        if ex_str == '':
            ex_str = 'SKIP'

        state_path = get_state_path(state)

        if state.inner_trans:
            in_str = ", ".join(translate_trans(tran, diagram) for tran in state.inner_trans)
        else:
            in_str = ""

        out_str = ""

        if not state.children:
            comp_str = "No_Composition"
        else:
            comp_str = translate_composition(ssid, diagram)
            if comp_str == '':
                comp_str = "No_Composition"
        
        return "State %s\n  (%s)\n  (%s)\n  (%s)\n  [%s]\n  [%s]\n  (%s)" % \
            (state_path, en_str, du_str, ex_str, in_str, out_str, comp_str)
    else:
        return ""

def translate_composition(ssid, diagram):
    state = diagram.all_states[ssid]
    if isinstance(state.children[0], OR_State):
        
        default_str = '['
        for i in range(len(state.children)):
            default_trans = state.children[i].default_tran
            if not default_trans:
                continue
            else:
                trans_str = translate_trans(default_trans, diagram)
                default_str += trans_str + ','
        if len(default_str) > 1:
            default_str = default_str[:-1] + ']'
        else:
            default_str = '[]'

        history_junc_str = 'False'
        if isinstance(state, OR_State) and state.has_history_junc == True:
            history_junc_str = 'True'
        
        name = state.get_state_whole_name()
        func_str = 'f_' + name
        return "Or (%s)\n (%s) (%s)" %(default_str, history_junc_str, func_str)
    elif isinstance(state.children[0], AND_State):
        children_list = list()
        for i in range(len(state.children)):
            children_list.append(state.children[i].name)
        tmp_str = '\'\', \'\''.join(children_list)
        children_str = '\'\'' + tmp_str + '\'\''

        name = state.get_state_whole_name()
        func_str = 'f_' + name
        return "And [%s]\n (%s)" %(children_str, func_str)

    else:
        return ""

#translate functions for Or/And Composition to get its children
def translate_composition_function(ssid, diagram):
    state = diagram.all_states[ssid]
    name = 'f_' + state.get_state_whole_name()
    fun_str = 'definition %s :: string2state where \n' %name
    def_str = ('%s_def' % name)
    fun_str += '\" %s = \n(λstr. ' %name
    for child in state.children:
        if not isinstance(child, Junction):
            child_name = child.get_state_whole_name()
            fun_str += 'if str = \'\'%s\'\' then %s else \n' %(child.name, child_name)
    fun_str += 'No_State )\"'
    return fun_str, def_str

#translate functions for junction to get its transition list
def translate_junction_function(diagram):
    fun_str = 'definition g :: juncs where \n'
    fun_str += '\" g = (λ str. '
    for ssid, state in diagram.all_states.items():
        if isinstance(state, Junction):
            junc_path = get_state_path(state)
            translist_str = '['
            for tran in state.out_trans:
                translist_str += translate_trans(tran, diagram)
                translist_str += ',\n'
            if translist_str[-1] == '\n':
                translist_str = translist_str[:-2] + ']'
            else:
                translist_str += ']'
            if translist_str != "[]":
                fun_str += 'if str = %s then %s else \n' %(junc_path, translist_str)
    for fun in diagram.diagram.funs:
        if not isinstance(fun, GraphicalFunction):
            continue
        for junction in fun.junctions:
            junc_path = get_state_path(junction)
            translist_str = '['
            for tran in junction.out_trans:
                translist_str += translate_trans(tran, diagram, True)
                translist_str += ',\n'
            if translist_str[-1] == '\n':
                translist_str = translist_str[:-2] + ']'
            else:
                translist_str += ']'
            fun_str += 'if str = %s then %s else \n' %(junc_path, translist_str) 
    fun_str += '[])\"'
    return fun_str

#转化顺序有要求，一定得先从最低一层转换，否则会报错
def dfs_search_chart(ssid, diagram, str, def_list):
    state = diagram.all_states[ssid]
    if isinstance(state, Junction):
        return str, def_list
    if not state.children:
        name = state.get_state_whole_name()
        str += 'definition %s :: state where \" %s = ' %(name, name)
        state_str = translate_state(ssid, diagram)
        str += state_str
        str += '\"\n\n'
        def_list.append('%s_def' %name)
    else:
        for child in state.children:
            child_ssid = child.ssid
            str, def_list = dfs_search_chart(child_ssid, diagram, str, def_list)
        fun_str, def_str = translate_composition_function(ssid, diagram)
        str += fun_str
        str += '\n\n'
        def_list.append(def_str)
        if not ssid == diagram.diagram.ssid:
            name = state.get_state_whole_name()
            str += 'definition %s :: state where \" %s = ' %(name, name)
            state_str = translate_state(ssid, diagram)
            str += state_str
            str += '\"\n\n'
            def_list.append('%s_def' %name)
        else:
            str += 'definition Root :: comp where \" Root = '
            comp_str = translate_composition(ssid, diagram)
            str += comp_str
            str += '\"\n\n'
            def_list.append('Root_def')
    return str, def_list


def translate_chart_info(chart):
    chart_str = 'definition I :: ctxt where \n'
    chart_str += '\"I str = ('
    str1 = '(Info False [] [])'
    for ssid, state in chart.all_states.items():
        if isinstance(state, Junction):
            continue
        state_path = get_state_path(state)
        if not state.children:
            chart_str += 'if str = %s then %s else\n' %(state_path,str1)
        elif isinstance(state.children[0], AND_State):
            chart_str += 'if str = %s then %s else\n' %(state_path,str1)
        elif isinstance(state.children[0], OR_State):
            chart_str += 'if str = %s then %s else\n' %(state_path,str1)
        else:
            continue
    
    chart_str += str1 + ')\"\n'
    return chart_str

def translate_fe_info(chart):
    fe_str = 'fe str = ('
    for fun in chart.diagram.funs:
        if not isinstance(fun, function.Function):
            continue
        fun_name = "\'\'" + fun.name + "\'\'"
        fenv_str = "(" + translate_action(fun.cmd, chart) + ',\n'
        tmp_str = ''
        str_end = ''
        for param in fun.params:
            tmp_str += '([[V \'\'%s\'\', ' %(param)
            str_end += ']])'
        tmp_str += ('No_Expr' + str_end)
        fenv_str += (tmp_str + ',\n')
        tmp_str = ''
        str_end = ''
        if fun.return_var is not None:
            if isinstance(fun.return_var, str):
                tmp_str += '([[V \'\'%s\'\', ' %(fun.return_var)
                str_end += ']])'
                tmp_str += ('No_Expr' + str_end)
            else:
                for var in fun.return_var:
                    tmp_str += '([[V \'\'%s\'\', ' %(var)
                    str_end += ']])'
                tmp_str += ('No_Expr' + str_end)
            fenv_str += (tmp_str + ')')
        else:
            fenv_str += ('No_Expr' + ')')
        fe_str += 'if str = %s then %s else \n' %(fun_name, fenv_str)
    fe_str += (("(SKIP, No_Expr, No_Expr)) \"") + '\n')
    #print(fe_str)
    return fe_str
            #print(procedures)
    
def translate_ge_info(chart):
    ge_str = 'ge str = ('
    for fun in chart.diagram.funs:
        if not isinstance(fun, GraphicalFunction):
            continue
        fun_name = "\'\'" + fun.name + "\'\'"
        genv_str = "((" + translate_trans(fun.default_tran, chart, True) + '),\n'
        tmp_str = ''
        str_end = ''
        for param in fun.params:
            tmp_str += '([[V \'\'%s\'\', ' %(param)
            str_end += ']])'
        tmp_str += ('No_Expr' + str_end)
        genv_str += (tmp_str + ',\n')
        tmp_str = ''
        str_end = ''
        if fun.return_var is not None:
            if isinstance(fun.return_var, str):
                tmp_str += '([[V \'\'%s\'\', ' %(fun.return_var)
                str_end += ']])'
                tmp_str += ('No_Expr' + str_end)
            else:
                for var in fun.return_var:
                    tmp_str += '([[V \'\'%s\'\', ' %(var)
                    str_end += ']])'
                tmp_str += ('No_Expr' + str_end)
            genv_str += (tmp_str + ')')
        else:
            genv_str += ('No_Expr' + ')')
        ge_str += 'if str = %s then %s else \n' %(fun_name, genv_str)
    ge_str += (("((Trans NONE (S []) (Bc True) SKIP SKIP NONE), No_Expr, No_Expr)) \"") + '\n')
    return ge_str
        

