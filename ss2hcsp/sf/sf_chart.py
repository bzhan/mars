import re
import lark

from ss2hcsp.sl.SubSystems.subsystem import Subsystem,Triggered_Subsystem
from ss2hcsp.sf.sf_state import AND_State, OR_State, Junction
from ss2hcsp.sf.sf_message import SF_Message
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AVar,AConst, BExpr, conj,disj
from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser
from ss2hcsp.hcsp.hcsp import Condition , Assign
from ss2hcsp.matlab import function

from ss2hcsp.hcsp.parser import aexpr_parser


def get_common_ancestor(state0, state1, tran_type="out_trans"):
    assert tran_type in ["out_trans", "inner_trans"]
    if state0 == state1:
        assert state0.father == state1.father
        if tran_type == "out_trans":
            return state0.father
        else:  # inner_trans
            return state0

    state_to_root = []
    cursor = state0
    while cursor:
        state_to_root.append(cursor)
        cursor = cursor.father

    cursor = state1
    while cursor not in state_to_root:
        cursor = cursor.father
    return cursor


def get_hcsp(hps,root):  # get the hcsp from a list of hps
    assert isinstance(hps, list)
    if not hps:
        return hp.Skip()

    _hps = []
    for i in range(len(hps)):
        assert hps[i]
        if isinstance(hps[i], hp.HCSP):
            if isinstance(hps[i], hp.OutputChannel) and (hps[i].ch_name.name.startswith("BR") or hps[i].ch_name.name.startswith("DBR")): #BR收到子图发来的消息广播申请
                # For example, hps[i].expr.name = E_S1
                #state_name = (lambda x: x[x.index("_") + 1:])(hps[i].expr.name)  # S1 split
                expr_name=hps[i].expr.name
                ch_expr=""
                state_name=""
                for event in root.event_list:
                    if event.name in expr_name:
                        state_name = expr_name[len(event.name)+1:]
                        #ch_expr = (lambda x: AConst('"' + x[:x.index("_")] + '"'))(hps[i].expr.name)  # AConst("e")
                        ch_expr = AConst('"'+event.name+'"')
                        break
                _hps.append(hp.OutputChannel(ch_name=hps[i].ch_name, expr=ch_expr))
                j = i + 1
                if hps[i].ch_name.name.startswith("BR"):
                    
                    if hps[j] != hp.Var("X"):  # hps[j] is VIn!
                        j += 1
                #assert hps[j] == hp.Var("X")
                if hps[i].ch_name.name.startswith("DBR"):
                    m=j
                    for k in range(m,len(hps)-1):
                        if isinstance(hps[k],(Assign)) and  hps[k] == hp_parser.parse("a_"+state_name+":= 0"):
                            j=k-1      
                            break
                        else:
                            j+=1         
                _hps.extend(hps[i + 1:j + 1])
                if len(hps) - 1 >= j + 1:
                    _hps.append(hp.Condition(cond=bexpr_parser.parse("a_" + state_name + " == 1"),
                                                 hp=get_hcsp(hps[j + 1:],root)))
                break
            else:
                if isinstance(hps[i], tuple):
                    assert len(hps[i]) == 2
                    cond = hps[i][0]
                    assert isinstance(cond, BExpr)
                    _hps.append(hp.Condition(cond=cond, hp=get_hcsp(hps[i][1],root)))
                _hps.append(hps[i])
        elif isinstance(hps[i], tuple):
            assert len(hps[i]) == 2
            cond = hps[i][0]
            assert isinstance(cond, BExpr)
            _hps.append(hp.Condition(cond=cond, hp=get_hcsp(hps[i][1],root)))


    if len(_hps) == 1:
        return _hps[0]
    else:
        return hp.Sequence(*_hps)
def parse_act_into_hp(acts, root, location):  # parse a list of actions of Simulink into an hcsp list
    assert isinstance(acts, (list, tuple,str))
    assert all(isinstance(act, str) for act in acts)
    assert isinstance(root, AND_State) and isinstance(location, (AND_State, OR_State))
    def get_name_from_mesg_list():
        name_list=list();
        for mesg in root.chart.local_message_queue+root.chart.input_message_queue:
            name_list.append(mesg.name)
        return name_list
    def _DBvout(_i, _vars):
            if not _vars:
                return "skip"
            for state in root.chart.all_states.values():
                if "a_"+state.name in _vars:
                    _vars.remove("a_"+state.name)
            if "E" in _vars:
                _vars.remove("E")
            if "done" in _vars:
                _vars.remove("done")
            return "; ".join("DBVOut" + str(_i) + "_" + _var + "?" + _var for _var in sorted(list(_vars)))
    def _DBvin(_i, _vars):
            if not _vars:
                return "skip"
            for state in root.chart.all_states.values():
                if "a_"+state.name in _vars:
                    _vars.remove("a_"+state.name)
            if "done" in _vars:
                _vars.remove("done")
            if "E" in _vars:
                _vars.remove("E")
            return "; ".join("DBVIn" + str(_i) + "_" + _var + "!" + _var for _var in sorted(list(_vars)))
    def get_child_hcsp(dest_state,root):
        hps=list()
        if isinstance(dest_state,(OR_State, AND_State)):
            _hps=list()
            # for s in root.chart.all_states.values():
            #     if dest_state.ssid == s.ssid:
            #         if s.is_parse_act == False:
            #             
            #             dest_state=s
                        
            #             break
            
            # root.chart.singal_state_parse_acts_on_states_and_trans(root.chart.all_states[dest_state.ssid])
            in_tran_hp = root.chart.execute_one_step_from_state(root.chart.all_states[dest_state.ssid]) 
            for child in dest_state.children:
                
                # for s in root.chart.all_states.values():
                #     if child.ssid == s.ssid:
                #         print(1111111111)
                #         if s.is_parse_act == False:
                #             
                #             child=s
                #             break
                
        
                _child_hp=get_child_hcsp(child,root)
                # cond=list()
                # if isinstance(child,(OR_State,AND_State)):
                #     cond.append(child.activated())
                #     conds = conj(*cond) if len(cond) >= 2 else cond[0]
                # root.chart.singal_state_parse_acts_on_states_and_trans(root.chart.all_states[child.ssid])
                # _hp=root.chart.execute_one_step_from_state(root.chart.all_states[child.ssid])
                if len(_child_hp)>0:
                    if all(isinstance(child, AND_State) for child in dest_state.children):
                        _hps.append(get_hcsp(_child_hp,root))
                    else:
                        _hps.append(hp.Condition(cond=bexpr_parser.parse("done == 0"),hp=get_hcsp(_child_hp,root)))
            if len(_hps)>0:
                hps.append(hp.Condition(dest_state.activated(),hp.Sequence(hp_parser.parse("done := 0"),in_tran_hp,hp.Sequence(*_hps) if len(_hps) >= 2 else  _hps[0] )))
            else:
                hps.append(hp.Condition(dest_state.activated(),hp.Sequence(hp_parser.parse("done := 0"),in_tran_hp)))
       
        return hps
    def get_dataStoreList():
        dataStorelists=list()
        for n,d in root.chart.data.items():
                    if d.scope == "DATA_STORE_MEMORY_DATA":
                        dataStorelists.append(d.name)
        return dataStorelists
    def is_dataStore(name):
        for n,d in root.chart.data.items():
                    if name == d.name and  d.scope == "DATA_STORE_MEMORY_DATA":
                        return d.name
        return None
    hps = list()
    # acts = action.split(";")
    Message_list=root.chart.local_message_queue + root.chart.input_message_queue
    # if len(Message_list)>=1:
    #     Message=Message_list[0]
    # else:
    #     Message=SF_Message("")
    name_lists=get_name_from_mesg_list()
    trigger_edge_osig =0
    for act in acts:
        if re.match(pattern="^(\\[)?\\w+(,\\w+)*(\\])? *:=.+$", string=act)  or re.match(pattern="^(\\[)?(\\w+(,)?)*(\\w+\\(\\w*(,\\w*)*\\))*((,)?\\w+)*((,)?\\w+\\(\\w*(,\\w*)*\\))*(\\])? *:=.+$", string=act) and "." not in act:  # an assigment   
            left,right=act.split(":=")
            left=left.strip()
            right=right.strip()
            if get_dataStoreList() is not None:
                DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                DSM_list=get_dataStoreList()
                for var in DSM_vars:
                    if var in DSM_list:
                        hps.append(hp_parser.parse("ch_"+var+"?"+var))   
            if  re.match(pattern="^\\w+\\(\\w*(,\\w+)*\\)", string=left):
                
                data_name = left[:left.index("(")]
                strs1=re.findall(r"[(](.*?)[)]", left)
                left_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                flag=0
                for n,d in root.chart.data.items():
                    if data_name == d.name and d.scope == "DATA_STORE_MEMORY_DATA":
                        flag=1
                        if len(left_exprs) == 1:
                            if left_exprs[0].isdigit():
                                left_exprs[0]=int(left_exprs[0])-1
                            else:
                                left_exprs[0]=left_exprs[0]+"-1"  
                            left = data_name + "["+str(left_exprs[0])+"]"
                        elif len(left_exprs) >1:
                            left_temp = data_name
                            for expr in left_exprs:
                                if expr.isdigit():
                                    expr=int(expr)-1
                                else:
                                    expr=expr+"-1"                                  
                                left_temp = left_temp + "["+str(expr)+"]"
                            left=left_temp
                        if re.match(pattern="^\\w+\\(\\w*(,\\w*)*\\)+$", string=right) or re.match(pattern="^\\w+$",string=right):
                            assert isinstance(root.chart, SF_Chart)
                            longest_path=root.chart.get_fun_by_path(str(right))
                            if longest_path is None:
                                # right =re.sub(pattern="(", repl="[", string=right)
                                # right =re.sub(pattern=")", repl="]", string=right)
                                if "(" in right:
                                    strs1=re.findall(r"[(](.*?)[)]", right)
                                    right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                                else:
                                    right_exprs=list()
                                if len(right_exprs) == 1:

                                    right = right[:right.index("(")]+"["+str(right_exprs[0])+"-1"+"]"+right[right.index(")")+1:]
                        
                                elif len(right_exprs) > 1:
                                    right_temp = right[:right.index("(")]
                                    for expr in right_exprs:
                                        if expr.isdigit():
                                            expr=int(expr)-1
                                        else:
                                            expr=expr+"-1"                                  
                                        right_temp = right_temp + "["+str(expr)+"]"
                                    right=right_temp+right[right.index(")")+1:]
                                hps.append(hp_parser.parse(left+":="+right))
                            else:
                                if "(" in right:
                                    strs1=re.findall(r"[(](.*?)[)]", right)
                                    right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                                else:
                                    right_exprs=list()
                                exprs=longest_path[1]
                                if exprs is not None and len(right_exprs) > 0:
                                    for  var in range(0,len(exprs)):
                                        hps.append(hp_parser.parse(str(exprs[var])+":="+str(right_exprs[var])))
                                return_var=longest_path[0]
                                if return_var is not None and len(left) >0:
                                    if isinstance(return_var,function.ListExpr):
                                        for  var in range(0,len(return_var)):
                                            hps.append(hp_parser.parse(str(return_var[var])+":= 0"))
                                    else:
                                        hps.append(hp_parser.parse(str(return_var)+":= 0"))
                                hps.append(root.chart.fun_dict[longest_path])

                                

                                if return_var is not None and len(left) >0:
                                    if isinstance(return_var,function.ListExpr):
                                        for  var in range(0,len(return_var)):
                                            hps.append(hp_parser.parse(left+":="+str(return_var[var])))
                                    else:
                                        hps.append(hp_parser.parse(left+":="+str(return_var)))
                        else:
                            if "(" in right:
                                strs1=re.findall(r"[(](.*?)[)]", right)
                                right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                            
                                if len(right_exprs) == 1:

                                    right = right[:right.index("(")]+"["+str(int(right_exprs[0])-1)+"]"+right[right.index(")")+1:]
                                   
                                elif len(right_exprs) > 1:
                                    right_temp = right[:right.index("(")]
                                    for expr in right_exprs:
                                        if expr.isdigit():
                                            expr=int(expr)-1
                                        else:
                                            expr=expr+"-1"                                  
                                        right_temp = right_temp + "["+str(expr)+"]"
                                    right=right_temp+right[right.index(")")+1:]
                            hps.append(hp_parser.parse(left+":="+right))
                        if get_dataStoreList() is not None:
                            DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                            DSM_list=get_dataStoreList()
                            for var in DSM_vars:
                                if var in DSM_list:
                                    hps.append(hp_parser.parse("ch_"+var+"!"+var))
                        break    
                if flag == 0:
                    
                    hps.append(hp_parser.parse(act))
                    if get_dataStoreList() is not None:
                        DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                        DSM_list=get_dataStoreList()
                        for var in DSM_vars:
                            if var in DSM_list:
                                hps.append(hp_parser.parse("ch_"+var+"!"+var))
            elif re.match(pattern="^(\\[)?\\w+(,\\w+)*(\\])?$", string=left) :  # a function
                    flag = 0
                    if "[" not in left:
                        for n,d in root.chart.data.items():

                            if left == d.name and d.scope == "DATA_STORE_MEMORY_DATA":
                                flag=1
                                if re.match(pattern="^\\w+\\(\\w*(,\\w*)*\\)+$", string=right) or re.match(pattern="^\\w+$",string=right):
                                    assert isinstance(root.chart, SF_Chart)
                                    longest_path=root.chart.get_fun_by_path(str(right))
                                    if longest_path is None:
                                        # right =re.sub(pattern="(", repl="[", string=right)
                                        # right =re.sub(pattern=")", repl="]", string=right)
                                        right_name=right[:right.index("(")] if "(" in right else right
                                        
                                        if "(" in right:
                                            strs1=re.findall(r"[(](.*?)[)]", right)
                                            right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                                            
                                        else:
                                            right_exprs=list()
                                        if len(right_exprs) == 1:
                                            if right_exprs[0].isdigit():
                                                right_exprs[0]=int(right_exprs[0])-1
                                            else:
                                                right_exprs[0]=right_exprs[0]+"-1" 
                                            right = right[:right.index("(")]+"["+str(right_exprs[0])+"]"+right[right.index(")")+1:]
                                            
                                        elif len(right_exprs) > 1:
                                            right_temp = right[:right.index("(")]
                                            for expr in right_exprs:
                                                if expr.isdigit():
                                                    expr=int(expr)-1
                                                else:
                                                    expr=expr+"-1"                                  
                                                right_temp = right_temp + "["+str(expr)+"]"
                                            right=right_temp+right[right.index(")")+1:]
                                        hps.append(hp_parser.parse(str(left+":="+right)))
                                    else:
                                        if "(" in right:
                                            strs1=re.findall(r"[(](.*?)[)]", right)
                                            right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                                        else:
                                            right_exprs=list()
                                        exprs=longest_path[1]
                                        if exprs is not None and len(right_exprs) > 0:
                                            for  var in range(0,len(exprs)):
                                                hps.append(hp_parser.parse(str(exprs[var])+":="+str(right_exprs[var])))
                                        return_var=longest_path[0]
                                        if return_var is not None and len(left) >0:
                                            if isinstance(return_var,function.ListExpr):
                                                for  var in range(0,len(return_var)):
                                                    hps.append(hp_parser.parse(str(return_var[var])+":= 0"))
                                            else:
                                                hps.append(hp_parser.parse(str(return_var[0])+":= 0"))
                                  
                                        hps.append(root.chart.fun_dict[longest_path])

                                        

                                        if return_var is not None and len(left) >0:
                                            if isinstance(return_var,function.ListExpr):
                                                for  var in range(0,len(return_var)):
                                                    hps.append(hp_parser.parse(left+":="+str(return_var[var])))
                                            else:
                                                hps.append(hp_parser.parse(left+":="+str(return_var[0])))
                                  
                                else:
                                    if "(" in right:
                                        strs1=re.findall(r"[(](.*?)[)]", right)
                                        right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                                    else:
                                        right_exprs=list()
                                    if len(right_exprs) == 1:

                                        right = right[:right.index("(")]+"["+str(int(right_exprs[0])-1)+"]"+right[right.index(")")+1:]
                                    elif len(right_exprs) > 1:
                                        right_temp = right[:right.index("(")]
                                        for expr in right_exprs:
                                            if expr.isdigit():
                                                expr=int(expr)-1
                                            else:
                                                expr=expr+"-1"                                  
                                            right_temp = right_temp + "["+str(expr)+"]"
                                        right=right_temp+right[right.index(")")+1:]
                                    hps.append(hp_parser.parse(str(left+":="+right)))
                                if get_dataStoreList() is not None:
                                            DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                                            DSM_list=get_dataStoreList()
                                            for var in DSM_vars:
                                                if var in DSM_list:
                                                    hps.append(hp_parser.parse("ch_"+var+"!"+var))

                    if flag ==0 or "[" in left:
                        
                        if re.match(pattern="^\\w+\\(\\w*(,\\w*)*\\)$", string=right) or re.match(pattern="^\\w+$",string=right) :
                            if "[" in left:
                                strs=left.strip('[').strip(']')
                                left=list(strs.split(",")) if  "," in strs else [strs]
                            else:
                               
                                left=[left]
                            assert isinstance(root.chart, SF_Chart)
                            if "(" in right:
                                strs1=re.findall(r"[(](.*?)[)]", right)
                                right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                            else:
                                right_exprs=list()
                            longest_path=root.chart.get_fun_by_path(str(right))
                            if longest_path is not None:
                                exprs=longest_path[1]
                                if exprs is not None and len(right_exprs) > 0:
                                    for  var in range(0,len(exprs)):
                                        hps.append(hp_parser.parse(str(exprs[var])+":="+str(right_exprs[var])))
                                return_var=longest_path[0]
                                if return_var is not None and len(left) >0:
                                    if isinstance(return_var,function.ListExpr):
                                        for  var in range(0,len(return_var)):
                                            if is_dataStore(left[var]):
                                                hps.append(hp_parser.parse(str(return_var[var])+":= 0"))
                                                # hps.append(hp_parser.parse("ch_"+left[var]+"!"+left[var]))
                                            else:
                                                hps.append(hp_parser.parse(str(return_var[var])+":= 0"))
                                hps.append(root.chart.fun_dict[longest_path])

                                

                                if return_var is not None and len(left) >0:
                                    if isinstance(return_var,function.ListExpr):
                                        for  var in range(0,len(return_var)):
                                            if is_dataStore(left[var]):
                                                hps.append(hp_parser.parse(str(left[var])+":="+str(return_var[var])))
                                                # hps.append(hp_parser.parse("ch_"+left[var]+"!"+left[var]))
                                            else:
                                                hps.append(hp_parser.parse(str(left[var])+":="+str(return_var[var])))
                                        if get_dataStoreList() is not None:
                                            DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                                            DSM_list=get_dataStoreList()
                                            for var in DSM_vars:
                                                if var in DSM_list:
                                                    hps.append(hp_parser.parse("ch_"+var+"!"+var))
                                    else:
                                        hps.append(hp_parser.parse(str(left[0])+":="+str(return_var[0])))
                                        if get_dataStoreList() is not None:
                                            DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                                            DSM_list=get_dataStoreList()
                                            for var in DSM_vars:
                                                if var in DSM_list:
                                                    hps.append(hp_parser.parse("ch_"+var+"!"+var))
                            else:
                                if "[" not in left:
                                    left =left[0]
                                if "(" in right:
                                    strs1=re.findall(r"[(](.*?)[)]", right)
                                    right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                               
                                    if len(right_exprs) == 1:
                                        if right_exprs[0].isdigit():
                                            right_exprs[0]=int(right_exprs[0])-1
                                        else:
                                            right_exprs[0]=right_exprs[0]+"-1" 
                                        right = right[:right.index("(")]+"["+str(right_exprs[0])+"]"+right[right.index(")")+1:]
                                       
                                    elif len(right_exprs) > 1:
                                        right_temp = right[:right.index("(")]
                                        for expr in right_exprs:
                                            if expr.isdigit():
                                                expr=int(expr)-1
                                            else:
                                                expr=expr+"-1"                                  
                                            right_temp = right_temp + "["+str(expr)+"]"
                                        right=right_temp+right[right.index(")")+1:]                       
                                    hps.append(hp_parser.parse(str(left+":="+right)))
                                    if get_dataStoreList() is not None:
                                        DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                                        DSM_list=get_dataStoreList()
                                        for var in DSM_vars:
                                            if var in DSM_list:
                                                hps.append(hp_parser.parse("ch_"+var+"!"+var))
                                else:

                                    hps.append(hp_parser.parse(str(left+":="+right)))
                                    if get_dataStoreList() is not None:
                                        DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                                        DSM_list=get_dataStoreList()
                                        for var in DSM_vars:
                                            if var in DSM_list:
                                                hps.append(hp_parser.parse("ch_"+var+"!"+var))
                        else:

                            hps.append(hp_parser.parse(act))
                            if get_dataStoreList() is not None:
                                DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                                DSM_list=get_dataStoreList()
                                for var in DSM_vars:
                                    if var in DSM_list:
                                        hps.append(hp_parser.parse("ch_"+var+"!"+var))
            else:
                if re.match(pattern="^\\w+\\(\\w*(,\\w*)*\\)$", string=right) or re.match(pattern="^\\w+$",string=right) :
                            if "[" in left:
                                strs=left.strip('[').strip(']')
                                left=list(strs.split(",")) if  "," in strs else [strs]
                            else:
                                left=[left]
                            assert isinstance(root.chart, SF_Chart)
                            if "(" in right:
                                strs1=re.findall(r"[(](.*?)[)]", right)
                                right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                            else:
                                right_exprs=list()
                            longest_path=root.chart.get_fun_by_path(str(right))
                            if longest_path is not None:
                                exprs=longest_path[1]
                                if exprs is not None and len(right_exprs) > 0:
                                    for  var in range(0,len(exprs)):
                                        hps.append(hp_parser.parse(str(exprs[var])+":="+str(right_exprs[var])))
                                return_var=longest_path[0]
                                if return_var is not None and len(left) >0:
                                    if isinstance(return_var,function.ListExpr):
                                        for  var in range(0,len(return_var)):
                                            hps.append(hp_parser.parse(str(return_var[var])+":= 0"))
                                    else:
                                        hps.append(hp_parser.parse(str(return_var)+":= 0"))
                                hps.append(root.chart.fun_dict[longest_path])

                                

                                if return_var is not None and len(left) >0:
                                    if isinstance(return_var,function.ListExpr):
                                        for  var in range(0,len(return_var)):
                                            if is_dataStore(left[var]):
                                                if "(" in left[var]:
                                                    strs2=re.findall(r"[(](.*?)[)]", left[var])
                                                    left_exprs2=list(strs2[0].split(",")) if  "," in strs2[0] else [strs2[0]]
                                                    if len(left_exprs2) ==1:
                                                        if left_exprs2[0].isdigit():
                                                            left_exprs2[0]=int(left_exprs2[0])-1
                                                        else:
                                                            left_exprs2[0]=left_exprs2[0]+"-1"
                                                        left[var] = left[var][:left[var].index("(")]+"["+str(left_exprs2[0])+"]"+left[var][left[var].index(")")+1:]
                                                
                                                hps.append(hp_parser.parse(str(left[var])+":="+str(return_var[var])))
                                                # hps.append(hp_parser.parse("ch_"+left[var]+"!"+left[var]))
                                            else:
                                                if "(" in left[var]:
                                                    # print(left[var])
                                                    # strs1=re.findall(r"[(](.*?)[)]", left[var])
                                                    # print(strs1)
                                                    # left_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                                                    # if len(left_exprs) == 1:
                                                    #     left[var] = left[var].replace("(", "[")
                                                    #     left[var] = left[var].replace(")", "]")
                                                    # elif len(left_exprs) >1:
                                                    #     left_temp = left[var][:left[var].index("(")]
                                                    #     for expr in left_exprs:
                                                    #         left_temp = left_temp + "["+expr+"]"
                                                    #     left[var]=left_temp
                                                
                                                    strs2=re.findall(r"[(](.*?)[)]", left[var])
                                                    left_exprs2=list(strs2[0].split(",")) if  "," in strs2[0] else [strs2[0]]
                                                    if len(left_exprs2) ==1:
                                                        if left_exprs2[0].isdigit():
                                                            left_exprs2[0]=int(left_exprs2[0])-1
                                                        else:
                                                            left_exprs2[0]=left_exprs2[0]+"-1"
                                                        left[var] = left[var][:left[var].index("(")]+"["+str(left_exprs2[0])+"]"+left[var][left[var].index(")")+1:]
                                                hps.append(hp_parser.parse(str(left[var])+":="+str(return_var[var])))
                                        if get_dataStoreList() is not None:
                                            DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                                            DSM_list=get_dataStoreList()
                                            for var in DSM_vars:
                                                if var in DSM_list:
                                                    hps.append(hp_parser.parse("ch_"+var+"!"+var))
                                    else:
                                        hps.append(hp_parser.parse(str(left[0])+":="+str(return_var)))
                                        if get_dataStoreList() is not None:
                                            DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                                            DSM_list=get_dataStoreList()
                                            for var in DSM_vars:
                                                if var in DSM_list:
                                                    hps.append(hp_parser.parse("ch_"+var+"!"+var))
                            else:
                                if "[" not in left:
                                    left =left[0]
                                if "(" in right:
                                    strs1=re.findall(r"[(](.*?)[)]", right)
                                    right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                                
                                    if len(right_exprs) == 1:

                                        right = right[:right.index("(")]+"["+str(int(right_exprs[0])-1)+"]"+right[right.index(")")+1:]
                                       
                                    elif len(right_exprs) > 1:
                                        right_temp = right[:right.index("(")]
                                        for expr in right_exprs:
                                            if expr.isdigit():
                                                expr=int(expr)-1
                                            else:
                                                expr=expr+"-1"                                  
                                            right_temp = right_temp + "["+str(expr)+"]"
                                        right=right_temp+right[right.index(")")+1:]
                                    hps.append(hp_parser.parse(str(left+":="+right)))
                                    if get_dataStoreList() is not None:
                                        DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                                        DSM_list=get_dataStoreList()
                                        for var in DSM_vars:
                                            if var in DSM_list:
                                                hps.append(hp_parser.parse("ch_"+var+"!"+var))
                                else:

                                    hps.append(hp_parser.parse(str(left+":="+right)))
                                    if get_dataStoreList() is not None:
                                        DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                                        DSM_list=get_dataStoreList()
                                        for var in DSM_vars:
                                            if var in DSM_list:
                                                hps.append(hp_parser.parse("ch_"+var+"!"+var))
                        # else:

                        #     hps.append(hp_parser.parse(act))
                        #     if get_dataStoreList() is not None:
                        #         DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                        #         DSM_list=get_dataStoreList()
                        #         for var in DSM_vars:
                        #             if var in DSM_list:
                        #                 hps.append(hp_parser.parse("ch_"+var+"!"+var))
                else:
                    if "[" in left:
                        strs=left.strip('[').strip(']')
                        left=list(strs.split(",")) if  "," in strs else [strs]
                    else:
                        left=[left]
                    if "[" in right:
                        strs=right.strip('[').strip(']')
                        right=list(strs.split(",")) if  "," in strs else [strs]
                    else:
                        right=[right]
                    for  var in range(0,len(left)):
                        if is_dataStore(left[var]):
                            hps.append(hp_parser.parse(str(left[var])+":="+str(right[var])))
                        else:
                            hps.append(hp_parser.parse(str(left[var])+":="+str(right[var])))
                    if get_dataStoreList() is not None:
                        DSM_vars=hp_parser.parse(act).var_name.get_vars().union(hp_parser.parse(act).expr.get_vars())
                        DSM_list=get_dataStoreList()
                        for var in DSM_vars:
                            if var in DSM_list:
                                hps.append(hp_parser.parse("ch_"+var+"!"+var))
        elif re.match(pattern="^\\w+\\(\\w*(\\()?\\w*(,\\w*)*(\\))?(,\\w*)*\\)$", string=act) and not re.match(pattern="send\\(.*?\\)", string=act):  # a function
            assert isinstance(root.chart, SF_Chart)
            # hps.append(root.chart.fun_dict[root.chart.get_fun_by_path(str(act))])
            right=act
            strs1=re.findall(r"[(](.*)[)]", right)
            right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
            longest_path=root.chart.get_fun_by_path(str(right))
            if longest_path is not None:
                exprs=longest_path[1]
                if exprs is not None and len(right_exprs) > 0:
                    for  var in range(0,len(exprs)):
                        if "(" in right_exprs[var]:
                            strs1=re.findall(r"[(](.*?)[)]", right_exprs[var])
                            right_exprs1=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                        
                            if len(right_exprs1) == 1:

                                right_exprs[var] = right_exprs[var][:right_exprs[var].index("(")]+"["+str(right_exprs1[0]+"-1")+"]"+right_exprs[var][right_exprs[var].index(")")+1:]
                               
                            elif len(right_exprs1) > 1:
                                right_temp = right_exprs[var][:right_exprs[var].index("(")]
                                for expr in right_exprs1:
                                    if expr.isdigit():
                                        expr=int(expr)-1
                                    else:
                                        expr=expr+"-1"                                  
                                    right_temp = right_temp + "["+str(expr)+"]"
                                right_exprs[var]=right_temp+right_exprs[var][right_exprs[var].index(")")+1:]
                        hps.append(hp_parser.parse(str(exprs[var])+":="+str(right_exprs[var])))
                hps.append(root.chart.fun_dict[longest_path])   
        
                                      
    
        if len(Message_list)>=1:
            if re.match(pattern="^\\w+\\.\\w+ *:=.+$", string=act):
                left,right=act.split(":=")
                left=left.strip()
                right=right.strip()
                left1,left2=left.split(".")
                for Message in Message_list:
                    if left1 == Message.name:
                        hps.append(hp_parser.parse(left1+"_"+left2+":="+right))
                        Message.data=int(right)
            elif re.match(pattern="send\\(.*?\\)", string=act)  :
                    acts=act.strip('send(').strip(')')
                    for Message in Message_list:
                        if  acts == Message.name:
                            hps.append(hp_parser.parse('M_'+Message.name+' := ""; ML_'+Message.name+' := [""]'+"; ML_"+Message.name+" := push(ML_"+Message.name+","+'"' + Message.name + '"'+")" ))
            # fun_path = tuple(act[:act.index("(")].split("."))
            # for path, fun in root.chart.fun_dict.items():
            #     assert len(fun_path) <= len(path) and isinstance(fun, hp.HCSP)
            #     if path[-len(fun_path):] == fun_path:
            #         hps.append(fun)
            #         break

        if (re.match(pattern="^\\w+$", string=act) and (str(act) not in name_lists) ) or (re.match(pattern="send\\(.*?\\)", string=act) and (str(act.strip('send(').strip(')')) not in name_lists)):
            if (re.match(pattern="^\\w+$", string=act)) or re.match(pattern="send\\(.*?,.*?\\)", string=act) or (re.match(pattern="send\\(.*?\\)", string=act)):  # an event
                assert isinstance(root.chart, SF_Chart)
                # root.chart.has_event = True
                root_num = re.findall(pattern="\\d+", string=root.name)
                assert len(root_num) == 1
                root_num = root_num[0]
                if re.match(pattern="^\\w+$", string=act) :
                    flag =0
                    for e in root.chart.event_list:
                        if e.name == act and e.scope == "OUTPUT_EVENT" :
                            if e.trigger == "FUNCTION_CALL_EVENT":
                                hps.append(hp_parser.parse("tri" + '!"' +e.name +'"'))
                            flag=1
                            break
                    if flag == 0: 
                        root.chart.has_event = True
                        event = act + "_" + location.name
                        hps.append(hp_parser.parse("BR" + root_num + "!" + event))
                        hps.append(hp.Var("X"))
                
                if re.match(pattern="send\\(.*?\\)", string=act):
                    acts=act.strip('send(').strip(')')
                    if re.match(pattern="send\\(.*?,.*?\\)", string=act) or "." in acts:
                        root.chart.has_event = True
                        if re.match(pattern="send\\(.*?,.*?\\)", string=act):
                            event , dest_state_name1 = [e.strip() for e in act[5:-1].split(",")]
                            path=dest_state_name1.split(".")
                            if "." in dest_state_name1:
                                path=dest_state_name1.split(".")
                                dest_state_name=path[len(path)-1]
                            else:
                                dest_state_name=dest_state_name1
                        elif "." in acts:
                            path=acts.split(".")
                            dest_state_name=path[len(path)-2]
                            event=path[len(path)-1]
                        _event=event + "_" + location.name
                        for state in root.chart.all_states.values():
                            if state.original_name == dest_state_name:
                                dest_state=state
                                break
                        _root=dest_state.root
                        _root_num=re.findall(pattern="\\d+", string=_root.name)
                        _root_num=_root_num[0]
                        # vars_in_s_i = root.get_vars().union(set(root.chart.port_to_in_var.values()))
                        vars_in_s_i=set([var_name for var_name, value in sorted(root.chart.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]]).union(set(root.chart.port_to_in_var.values()))
                        vars_in_s_i1 =set([var_name for var_name, value in sorted(_root.chart.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]]).union(set(root.chart.port_to_in_var.values()))
                        hps.append(hp_parser.parse("DBR" + root_num + "!" + _event))
                        hps.append(hp_parser.parse(_DBvin(root_num, vars_in_s_i)))
                        hps.append(hp_parser.parse("DBnum"+root_num+"!"+_root_num))
                        if dest_state.name == _root.name:
                           print("dest_state is a parallel state")
                           hps.append(hp_parser.parse('DState'+root_num+'! "'+'"'))
                           hps.append(hp_parser.parse("DBO" +root_num + "!"))
                           hps.append(hp_parser.parse(_DBvin(root_num, vars_in_s_i)))
                        else:
                            name="a_"+dest_state.name
                            if _root.name != root.name:
                                root.chart.dest_state_root_num=_root_num
                                root.chart.dest_state_name=dest_state.name
                                hps.append(hp_parser.parse('DState'+root_num+'! "'+name+'"'+""))
                                hps.append(hp_parser.parse("DBO" +root_num + "!;"+ _DBvin(root_num, vars_in_s_i)))
                                #hps.append(hp.Sequence(get_hcsp(_root.init()), get_hcsp(_root.activate()),get_hcsp(get_child_hcsp(dest_state,root))))
                            else:
                                hps.append(hp.Sequence( hp_parser.parse('DState'+root_num+'! "'+'"'+""+";DBC" + _root_num + "?E;"+ _DBvout(_root_num, vars_in_s_i1)),get_hcsp(get_child_hcsp(dest_state,root),root),hp_parser.parse("DBO" +root_num + "!;"+ _DBvin(root_num, vars_in_s_i)),hp_parser.parse("DBC" + _root_num + "?E;"+ _DBvout(_root_num, vars_in_s_i1))))
                                #hps.append()

                        # if isinstance(dest_state,(OR_State, AND_State)):
                        #     in_tran_hp = root.chart.execute_one_step_from_state(dest_state) 
                        #     for child in dest_state.children:
                        #         cond=list()
                        #         cond.append(child.activated())
                        #         conds = conj(*cond) if len(cond) >= 2 else cond[0]
                        #         _hp=root.chart.execute_one_step_from_state(child)
                        #         _hps.append(hp.Condition(cond=conds,hp=hp.Sequence(hp_parser.parse("done := 0"),_hp)))
                        #     if len(_hps)>0:

                        #         hps.append(hp.Condition(dest_state.activated(),hp.Sequence(hp_parser.parse("done := 0"),in_tran_hp,hp.Condition(bexpr_parser.parse("done == 0"),hp.Sequence(*_hps) if len(_hps) >= 2 else  _hps[0] ))))
                        #     else:
                        #         hps.append(hp.Condition(dest_state.activated(),hp.Sequence(hp_parser.parse("done := 0"),in_tran_hp)))
                        
                    elif re.match(pattern="send\\(.*?\\)", string=act):
                        event_name=act.strip('send(').strip(')')
                        flag =0
                        for event in root.chart.event_list:
                                                       
                            if event_name == event.name and event.scope == "OUTPUT_EVENT" and event.trigger == "FUNCTION_CALL_EVENT":
                                flag=1
                                hps.append(hp_parser.parse("tri" + '!"' +event_name+'"' ))
                            elif event_name == event.name and event.scope == "OUTPUT_EVENT":
                                flag=1
                                wait_time=root.chart.max_step
                                if trigger_edge_osig == 0:
                                    hps.append(hp.Sequence(
                                                hp.Assign("out_tri", AConst(trigger_edge_osig)),
                                                hp.OutputChannel('ch_' + 'trig', AVar("out_tri")),
                                                hp.Wait(AConst(wait_time)),
                                                hp_parser.parse("state_time := state_time +"+str(root.chart.st)),
                                                hp.Assign("out_tri", AConst(1)),
                                                hp.OutputChannel('ch_' + 'trig', AVar("out_tri"))
                                                # hp.Assign("out_tri",AConst(1)), 
                                                # hp.Condition(cond=final_cond, hp=hp_parser.parse("tri"+'! "'+tri_event+'"'+""))              
                                                ))
                                    trigger_edge_osig =1
                                else:
                                    hps.append(hp.Sequence(
                                                hp.Assign("out_tri", AConst(trigger_edge_osig)),
                                                hp.OutputChannel('ch_' + 'trig', AVar("out_tri")),
                                                hp.Wait(AConst(wait_time)),
                                                hp_parser.parse("state_time := state_time +"+str(root.chart.st)),
                                                hp.Assign("out_tri", AConst(0)),
                                                hp.OutputChannel('ch_' + 'trig', AVar("out_tri"))
                                                
                                                ))
                                    trigger_edge_osig =0
               
                        if flag == 0: 
                            root.chart.has_event = True
                            event = (act.strip('send(').strip(')')) + "_" + location.name
                            hps.append(hp_parser.parse("BR" + root_num + "!" +event ))
                            hps.append(hp.Var("X"))
             
            
    return hps


class SF_Chart(Subsystem):
    def __init__(self, name, state, data, num_src, num_dest, st=0.1,input_message_queue=None,local_message_queue=None,event_list=None, is_triggered_chart=False,trigger_dest=None,trigger_type="",sf_charts=None,max_step=0.2):
        super(SF_Chart, self).__init__(name, num_src, num_dest)

        self.type = "stateflow"
        self.num_src = 10
        self.num_dest = num_dest
        self.src_lines = [[] for _ in range(self.num_src)]  # [[]] * self.num_src
        self.dest_lines = [None] * self.num_dest

        assert isinstance(state, (AND_State,OR_State))
        self.diagram = state
        self.diagram.chart = self

        self.all_states = state.get_all_descendants() # dict
        assert self.diagram.ssid not in self.all_states
        self.all_states[self.diagram.ssid] = self.diagram

        # The dictionary of functions in stateflow,
        # in form of {path (tuple): function (hcsp)}
        self.fun_dict = state.get_fun_dict()
        self.mesg_hp=list()
        self.has_event = False  # if the acts in the sf_chart have any broadcast event

        self.data = data
        self.all_vars = sorted(data.keys())

        self.st = 2

        self.port_to_in_var = dict()
        self.port_to_out_var = dict()
        self.triggerport_to_in_var=dict()
        self.triggerport_to_out_var=dict()

        self.dest_state_root_num=-1
        self.dest_state_name=""
        if input_message_queue is None:
            input_message_queue = []
        self.input_message_queue=input_message_queue
        if local_message_queue is None:
            local_message_queue = []
        self.local_message_queue=local_message_queue
        if  event_list is None:
            event_list = []
        self.event_list=event_list
        self.is_triggered_chart=is_triggered_chart
        if  trigger_dest is None:
            trigger_dest = []
        self.trigger_dest=trigger_dest
        self.trigger_type=trigger_type
        if sf_charts is None:
            sf_charts = {}
        self.sf_charts=sf_charts
        self.max_step=max_step
        funs_state_name=list()
        children_list=list()

        # for fun in state.funs:
        #     if fun.type == "GRAPHICAL_FUNCTION":
        #             funs_state_name.append(fun.chart_state1.original_name)

        for s in state.children:
            if s.original_name not in funs_state_name:
                # print(s.original_name )
                children_list.append(s)
        state.children=children_list   
        for state in self.all_states.values():
            if isinstance(state,(AND_State,OR_State)):
                state.whole_name=state.get_state_whole_name()       
        # self.add_names()
        # self.find_root_for_states()
        # self.find_root_and_loc_for_trans()
        # self.parse_acts_on_states_and_trans()
        # for fun in self.diagram.funs:
        #     for state in self.all_states.values():
        #         if fun.chart_state1 is not None: 
        #             if state.name == fun.chart_state1.name:
        #                 hps=hp.Sequence(hp_parser.parse("done := 0"),get_hcsp(state.activate(),self),self.execute_one_step_from_state(state),state._exit()) 
        #                 fun.script=hps
    def add_state_time(self):
        add_state_time=list()
        for s in self.all_states.values():
                if isinstance(s,OR_State) and s.has_aux_var("state_time"+str(s.ssid)):
                    add_state_time.append(hp_parser.parse("state_time"+str(s.ssid)+" := "+"state_time"+str(s.ssid)+"+"+str(self.st)))
        return add_state_time

    def __str__(self):
        return "Chart(%s):\n%s" % (self.name, str(self.diagram))

    def add_names(self):  # add names to states and junctions
        self.diagram.name = "S1"
        if self.diagram.children:
            if isinstance(self.diagram.children[0], AND_State):
                self.diagram.name = "S0"
                num = 1
                for child in self.diagram.children:
                    child.name = "S" + str(num)
                    num += 1

        and_num = or_num = jun_num = 0
        for state in self.all_states.values():
            if not state.name:
                if isinstance(state, AND_State):
                    state.name = "AND" + str(and_num)
                    and_num += 1
                elif isinstance(state, OR_State):
                    state.name = "OR" + str(or_num)
                    or_num += 1
                elif isinstance(state, Junction):
                    state.name = "Jun" + str(jun_num)
                    jun_num += 1
                else:
                    raise RuntimeError("Error State!")

    def find_root_for_states(self):  # get the root of each state in chart
        def find_root_recursively(_state):
            if isinstance(_state, (AND_State, OR_State)) and _state.father:
                _state.root = _state.father.root             
                for _child in _state.children:
                    find_root_recursively(_child)

        if self.diagram.name == "S0":
            for child in self.diagram.children:
                assert isinstance(child, AND_State)
                child.root = child
                child.chart = self
                for grandchild in child.children:
                    find_root_recursively(grandchild)
        elif self.diagram.name == "S1":
            assert self.diagram.chart == self
            for state in self.all_states.values():
                state.root = self.diagram
        else:
            raise RuntimeError("add_names() should be executed in advance!")

    def find_root_and_loc_for_trans(self):  # get root and location for each transition in chart
        for state in self.all_states.values():
            if hasattr(state, "default_tran") and state.default_tran:
                state.default_tran.root = state.root
                state.default_tran.location = state.father
            out_trans = list(state.out_trans) if hasattr(state, "out_trans") else list()
            for tran in out_trans:
                tran.root = state.father.root if isinstance(state, Junction) else state.root
                src_state = self.all_states[tran.src]
                dst_state = self.all_states[tran.dst]
                tran.location = get_common_ancestor(src_state, dst_state, "out_trans")
            inner_trans = list(state.inner_trans) if hasattr(state, "inner_trans") else list()
            for tran in out_trans + inner_trans:
                tran.root = state.father.root if isinstance(state, Junction) else state.root
                src_state = self.all_states[tran.src]
                dst_state = self.all_states[tran.dst]
                tran.location = get_common_ancestor(src_state, dst_state, "inner_trans")

    def singal_state_parse_acts_on_states_and_trans(self,state):
        if self.all_states[state.ssid].is_parse_act == False:
               
                self.all_states[state.ssid].is_parse_act=True
                if isinstance( self.all_states[state.ssid], (AND_State, OR_State)):
                    if  self.all_states[state.ssid].en:
                         self.all_states[state.ssid].en = parse_act_into_hp(acts= self.all_states[state.ssid].en, root= self.all_states[state.ssid].root, location= self.all_states[state.ssid])
                    if  self.all_states[state.ssid].du:
                        self.all_states[state.ssid].du = parse_act_into_hp(acts= self.all_states[state.ssid].du, root= self.all_states[state.ssid].root, location= self.all_states[state.ssid])
                    if  self.all_states[state.ssid].ex:
                         self.all_states[state.ssid].ex = parse_act_into_hp(acts= self.all_states[state.ssid].ex, root= self.all_states[state.ssid].root, location= self.all_states[state.ssid])
                    if hasattr( self.all_states[state.ssid], "default_tran") and  self.all_states[state.ssid].default_tran:
                        cond_acts =  self.all_states[state.ssid].default_tran.cond_acts
                        tran_acts =  self.all_states[state.ssid].default_tran.tran_acts
                        root =  self.all_states[state.ssid].default_tran.root
                        location =  self.all_states[state.ssid].default_tran.location
                        self.all_states[state.ssid].default_tran.cond_acts = parse_act_into_hp(cond_acts, root, location)
                        self.all_states[state.ssid].default_tran.tran_acts = parse_act_into_hp(tran_acts, root, location)
                    out_trans = list( self.all_states[state.ssid].out_trans) if hasattr( self.all_states[state.ssid], "out_trans") else list()
                    inner_trans = list( self.all_states[state.ssid].inner_trans) if hasattr( self.all_states[state.ssid], "inner_trans") else list()
                    for tran in out_trans + inner_trans:
                        tran.cond_acts = parse_act_into_hp(tran.cond_acts, tran.root, self.get_state_by_ssid(tran.src))                  
                        tran.tran_acts = parse_act_into_hp(tran.tran_acts, tran.root, self.get_state_by_ssid(tran.src))
                elif isinstance( self.all_states[state.ssid], Junction):
                    if hasattr( self.all_states[state.ssid], "default_tran") and  self.all_states[state.ssid].default_tran:
                        cond_acts =  self.all_states[state.ssid].default_tran.cond_acts
                        tran_acts =  self.all_states[state.ssid].default_tran.tran_acts
                        root =  self.all_states[state.ssid].default_tran.root
                        location =  self.all_states[state.ssid].default_tran.location
                        self.all_states[state.ssid].default_tran.cond_acts = parse_act_into_hp(cond_acts, root, location)
                        self.all_states[state.ssid].default_tran.tran_acts = parse_act_into_hp(tran_acts, root, location)
                    for tran in  self.all_states[state.ssid].out_trans:
                        tran.cond_acts = parse_act_into_hp(tran.cond_acts, tran.root, tran.location)
                        tran.tran_acts = parse_act_into_hp(tran.tran_acts, tran.root, tran.location)
                else:
                    print( self.all_states[state.ssid], type( self.all_states[state.ssid]))
                    raise RuntimeError("Error State!")
    def parse_acts_on_states_and_trans(self):
        for state in self.all_states.values():
            if state.is_parse_act == False:
                state.is_parse_act=True
                if isinstance(state, (AND_State, OR_State)):
                    if state.en:
                        state.en = parse_act_into_hp(acts=state.en, root=state.root, location=state)
                    if state.du:
                        state.du = parse_act_into_hp(acts=state.du, root=state.root, location=state)
                    if state.ex:
                        state.ex = parse_act_into_hp(acts=state.ex, root=state.root, location=state)
                    if hasattr(state, "default_tran") and state.default_tran:
                        cond_acts = state.default_tran.cond_acts
                        tran_acts = state.default_tran.tran_acts
                        root = state.default_tran.root
                        location = state.default_tran.location
                        state.default_tran.cond_acts = parse_act_into_hp(cond_acts, root, location)
                        state.default_tran.tran_acts = parse_act_into_hp(tran_acts, root, location)
                    out_trans = list(state.out_trans) if hasattr(state, "out_trans") else list()
                    inner_trans = list(state.inner_trans) if hasattr(state, "inner_trans") else list()
                    for tran in out_trans + inner_trans:
                        tran.cond_acts = parse_act_into_hp(tran.cond_acts, tran.root, self.get_state_by_ssid(tran.src))                  
                        tran.tran_acts = parse_act_into_hp(tran.tran_acts, tran.root, self.get_state_by_ssid(tran.src))
                elif isinstance(state, Junction):
                    if hasattr(state, "default_tran") and state.default_tran:
                        cond_acts = state.default_tran.cond_acts
                        tran_acts = state.default_tran.tran_acts
                        root = state.default_tran.root
                        location = state.default_tran.location
                        state.default_tran.cond_acts = parse_act_into_hp(cond_acts, root, location)
                        state.default_tran.tran_acts = parse_act_into_hp(tran_acts, root, location)
                    for tran in state.out_trans:
                        tran.cond_acts = parse_act_into_hp(tran.cond_acts, tran.root, tran.location)
                        tran.tran_acts = parse_act_into_hp(tran.tran_acts, tran.root, tran.location)
                else:
                    print(state, type(state))
                    raise RuntimeError("Error State!")

    def get_state_by_whole_name(self, name):
        for state in self.all_states.values():
            if state.whole_name == name:
                return state
    def get_state_by_name(self, name):
        for state in self.all_states.values():
            if state.name == name:
                return state
    def get_state_by_ssid(self, ssid):
        for state in self.all_states.values():
            if state.ssid == ssid:
                return state
    def get_fun_by_path(self, fun_path):       
        assert isinstance(fun_path, str)
        if "(" in fun_path:
            fun_path1=fun_path
            fun_path = tuple(fun_path[:fun_path.index("(")].split("."))
        else:
            fun_path = tuple(fun_path[:].split("."))
        matched_paths = []
        for path, fun in self.fun_dict.items():
          
            return_var=path[0]
            path1=path[2:]
            assert len(fun_path) <= len(path1)
            # assert len(fun_path) <= len(path1) and isinstance(fun, hp.HCSP)
            if path1[-len(fun_path):] == fun_path :
                matched_paths.append(path)
        if matched_paths:
            assert matched_paths
            path_lengths = [len(path) for path in matched_paths]
            assert len(path_lengths) == len(set(path_lengths))
            longest_path = matched_paths[path_lengths.index(max(path_lengths))]
        else:
            longest_path = None
        if longest_path is not None:
            fun_hp=self.fun_dict[longest_path]
           
            if isinstance(fun_hp,OR_State):
                if not self.all_states[fun_hp.ssid].is_parse_act:
                    for f in self.all_states[fun_hp.ssid].children:
                        self.singal_state_parse_acts_on_states_and_trans(self.all_states[f.ssid])

                hps=hp.Sequence(hp_parser.parse("done := 0"),get_hcsp(self.all_states[fun_hp.ssid].activate(),self),self.execute_one_step_from_state(self.all_states[fun_hp.ssid]))
                self.fun_dict[longest_path]=hps
        return longest_path     

    # Execute one step from a state
    def execute_one_step_from_state(self, state):
        
        def are_instances(objects, classes):
            assert len(objects) == len(classes)
            return all(isinstance(_obj, _class) for _obj, _class in zip(objects, classes))

        # Transfer an object into a Condition one if it is of ITE with len(if_hps) == 1 and else_hp == hp.Skip()
        def to_Condition(obj):
            
            if isinstance(obj, hp.ITE) and len(obj.if_hps) == 1 and obj.else_hp == hp.Skip(): 
                return hp.Condition(cond=obj.if_hps[0][0], hp=obj.if_hps[0][1])
            return obj
        
        message=None
        for message in self.input_message_queue+self.local_message_queue:
            message=message
        # Get the result hcsp of executing outgoing and inner transitions from state
        out_tran_hp,hp_fun_onCon= self.execute_trans_from_state(state, tran_type="out_trans")  
        assert isinstance(out_tran_hp, (hp.Skip, hp.ITE))
        in_tran_hp,hp_fun_onCon1 = self.execute_trans_from_state(state, tran_type="inner_trans")
        assert isinstance(in_tran_hp, (hp.Skip, hp.ITE))

        # Get during action
        during_hp=hp.Skip()
        if isinstance(state,(OR_State,AND_State)):
            during_hp = get_hcsp(state.du,self) if state.du else hp.Skip()

        # Composite out_tran_hp, during_hp and in_tran_hp
        comp = [out_tran_hp, during_hp, in_tran_hp]
        if are_instances(comp, [hp.Skip, hp.Skip, hp.Skip]):
            return hp.Skip()
        if are_instances(comp, [hp.Skip, hp.Skip, hp.ITE]):
            if len(self.mesg_hp)>=1:
                return hp.Sequence( self.mesg_hp[0],to_Condition(in_tran_hp))
                self.mesg_hp=list()
            else:
                if isinstance(hp_fun_onCon1,hp.Skip):
                    return to_Condition(in_tran_hp)
                else:
                    return hp.Sequence(hp_fun_onCon1,to_Condition(in_tran_hp))
        if are_instances(comp, [hp.Skip, hp.HCSP, hp.Skip]):
            assert not isinstance(during_hp, hp.Skip)
            return during_hp
        if are_instances(comp, [hp.Skip, hp.HCSP, hp.ITE]):
            assert not isinstance(during_hp, hp.Skip)
            if len(self.mesg_hp)>=1:
                hp.Sequence(during_hp, self.mesg_hp[0],to_Condition(in_tran_hp))
                self.mesg_hp=list()
            else:
                if isinstance(hp_fun_onCon1,hp.Skip):
                    return hp.Sequence(during_hp, to_Condition(in_tran_hp))
                else:
                    return hp.Sequence(during_hp,hp_fun_onCon1, to_Condition(in_tran_hp))
        if are_instances(comp, [hp.ITE, hp.Skip, hp.Skip]):
            if len(self.mesg_hp)>=1:
                return hp.Sequence(self.mesg_hp[0],to_Condition(out_tran_hp))
                self.mesg_hp=list()
            else:
                if isinstance(hp_fun_onCon,hp.Skip):
                    return to_Condition(out_tran_hp)
                else:
                    return hp.Sequence(hp_fun_onCon, to_Condition(out_tran_hp))
        if are_instances(comp, [hp.ITE, hp.Skip, hp.ITE]):
            assert out_tran_hp.else_hp == hp.Skip()
            if len(self.mesg_hp)>=1:
                out_tran_hp.else_hp=hp.Sequence( self.mesg_hp[0],to_Condition(in_tran_hp))
                self.mesg_hp=list()
            else:
                if isinstance(hp_fun_onCon1,hp.Skip):
                    out_tran_hp.else_hp = to_Condition(in_tran_hp)
                else:
                    out_tran_hp.else_hp =hp.Sequence(hp_fun_onCon1, to_Condition(in_tran_hp)) 
            if isinstance(hp_fun_onCon,hp.Skip):
                return out_tran_hp
            else:
                return hp.Sequence(hp_fun_onCon,out_tran_hp)
        if are_instances(comp, [hp.ITE, hp.HCSP, hp.Skip]):
            assert not isinstance(during_hp, hp.Skip) and out_tran_hp.else_hp == hp.Skip()
            out_tran_hp.else_hp = during_hp
            if isinstance(hp_fun_onCon,hp.Skip):
                return out_tran_hp
            else:
                return hp.Sequence(hp_fun_onCon,out_tran_hp)
        if are_instances(comp, [hp.ITE, hp.HCSP, hp.ITE]):
            assert not isinstance(during_hp, hp.Skip) and out_tran_hp.else_hp == hp.Skip()
            if len(self.mesg_hp)>=1:
                out_tran_hp.else_hp=hp.Sequence( during_hp,self.mesg_hp[0], to_Condition(in_tran_hp))
                self.mesg_hp=list()
            else:
                if isinstance(hp_fun_onCon1,hp.Skip):
                    out_tran_hp.else_hp = hp.Sequence(during_hp, to_Condition(in_tran_hp))
                else:
                    out_tran_hp.else_hp = hp.Sequence(during_hp,hp_fun_onCon1,to_Condition(in_tran_hp))
            if isinstance(hp_fun_onCon,hp.Skip):
                return out_tran_hp
            else:
                return hp.Sequence(hp_fun_onCon,out_tran_hp)

    # Execute transitions from a state
    def execute_trans_from_state(self, state, tran_type="out_trans", tran_act_Q=(), event_var="E"):
        """
        Execute a set of transitions from a given state
        :param state: a given state
        :param tran_type: either outgoing transitions or inner ones
        :param tran_act_Q: queue of actions on transitions
        :param event_var: event variable, E default
        :return: an hcsp (an ITE or Skip object) of execution result
        """
        def get_loop_hps(dst_state,dst_trans):
            if_hp1=list()
            for tran in dst_trans:
                
                dst_state1 = self.all_states[tran.dst]
                process_name = dst_state.processes[-1][1]
                if dst_state1.visited:
                    if dst_state1 == dst_state:
                        # process_name = dst_state.processes[-1][0]
                        # hp_loop.append(hp.Var(process_name))
                        if_hp1.append((process_name.if_hps[0][0],hp.Sequence(process_name.if_hps[0][1])))
                        break
                    else:
                        process_name1 =None
                        process_name1 = dst_state1.processes[-1][1]
                        if process_name1 is not None:
                        # hp_loop.append(process_name1)
                            if_hp2=get_loop_hps(dst_state,dst_state1.out_trans)
                            if len(if_hp2) >0:
                                if_hp1.append((process_name1.if_hps[0][0],hp.Sequence(process_name1.if_hps[0][1],hp.ITE(if_hp2,hp.Skip()))))
                                
                            else:
                                # print(999)
                                # print(if_hp1)
                                if_hp1.append((process_name1.if_hps[0][0],hp.Sequence(process_name1.if_hps[0][1])))
                                                    

            return if_hp1
            # return hp_loop
        assert tran_type in ["out_trans", "inner_trans"]

        # An AND-state has no outgoing transitions
        # A Junction has no inner transitions
        # default_trans=list()
        if isinstance(state,(OR_State,AND_State)) and len(state.children)>0 and isinstance( state.children[0],Junction):
            for s in state.children:
                if s.default_tran is not None:
                    state = s
                    num = len(state.processes)
                    process_name = state.name+str(num)
                    state.processes.append((process_name,hp.Skip()))
                    state.visited =True

        if isinstance(state, AND_State) and tran_type == "out_trans" \
                or isinstance(state, Junction) and tran_type == "inner_trans":
            return hp.Skip(),hp.Skip()
        if tran_type == "out_trans":
            assert isinstance(state, (OR_State, Junction))
            trans = state.out_trans
        elif tran_type == "inner_trans":  # tran_type == "inner_trans"
            assert isinstance(state, (OR_State, AND_State))
            trans = state.inner_trans
        # state must be the source of each transition in trans
        assert all(state.ssid == tran.src for tran in trans)
        
        if_hps, else_hp = list(), hp.Skip()
        hp_fun_onCon=list()
        for tran in trans:
            for message in self.input_message_queue+self.local_message_queue:
                if tran.event == message.name:
                    event_var = "M_"+tran.event
                    self.mesg_hp.append(hp_parser.parse("ML_"+tran.event+" != [] ->( M_"+tran.event+" :=top(ML_"+tran.event+"); ML_"+tran.event+" :=pop(ML_"+tran.event+"))" ))
            conds = list()
            conds_event = list()
            edge_trigger_cond=""
            trigger_conds=list()
            
            if isinstance(state,(AND_State,OR_State)):
                root_num=re.findall(pattern="\\d+", string=state.root.name)
                if self.dest_state_root_num == root_num[0]:
                    conds.append(bexpr_parser.parse( "state" +'== "'+"a_"+state.name +'"'))
            if tran.event:
                flag=0      
                for event in self.event_list:
                    if event.name == tran.event and ( event.trigger in ["EITHER_EDGE_EVENT","FALLING_EDGE_EVENT","RISING_EDGE_EVENT"] )and event.scope =="INPUT_EVENT":
                        flag=1
                        conds_event.append(bexpr_parser.parse('"'+event.name +'"== "'+ tran.event +'"'))
                        break
                if flag == 0:
                    conds_event.append(bexpr_parser.parse(event_var +' == "'+ tran.event +'"'))      
                    if self.is_triggered_chart and self.trigger_type == "function-call":
                        trigger_conds.append(bexpr_parser.parse(event_var + ' == "'+ tran.event +'"'))
                        trigger_conds.append(bexpr_parser.parse("tri_event"+ ' == "'+ tran.event +'"'))
                        conds_event.clear()
                        conds_event.append(disj(*trigger_conds) if len(trigger_conds) >= 2 else trigger_conds[0])
            if tran.condition:     
                if "&&" in str(tran.condition) or "||" in str(tran.condition):
                    if "&&" in str(tran.condition):
                        conditions=str(tran.condition).split("&&")
                    if "||" in str(tran.condition):
                        conditions=str(tran.condition).split("||")
                else:
                    conditions=[tran.condition]
                for condition in conditions:
                    if "==" in str(condition) or ">=" in str(condition) or "<=" in str(condition) or "<" in str(condition) or ">" in str(condition):
                        op=""
                        if "==" in str(condition):
                            left1,right1=str(condition).split("==")
                            op = "=="
                        elif "<=" in str(condition):
                            left1,right1=str(condition).split("<=")
                            op = "<="
                        elif ">=" in str(condition):
                            left1,right1=str(condition).split(">=")
                            op =">="
                        elif ">" in str(condition):
                            left1,right1=str(condition).split(">")
                            op = ">"
                        elif  "<" in str(condition):
                            left1,right1=str(condition).split("<")
                            op ="<"
                        left=left1.strip()
                        right=right1.strip()
                        if re.match(pattern="^\\w+\\(\\w*(,\\w*)*\\)$", string=right) or re.match(pattern="^\\w+$",string=right):
                            
                                longest_path=self.get_fun_by_path(str(right))
                                if longest_path is None:
                                    if "(" in right:
                                        strs1=re.findall(r"[(](.*?)[)]", right)
                                        right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]                    
                                    else:
                                        right_exprs=list()
                                    if len(right_exprs) == 1:
                                        if right_exprs[0].isdigit():
                                                right_exprs[0]=int(right_exprs[0])-1
                                        else:
                                                right_exprs[0]=right_exprs[0]+"-1"
                                        right=right[:right.index("(")]+"["+str(right_exprs[0])+"]"+right[right.index(")")+1:]
                                    elif len(right_exprs) > 1:
                                        right_temp = right[:right.index("(")]
                                        for expr in right_exprs:
                                            if expr.isdigit():
                                                expr=int(expr)-1
                                            else:
                                                expr=expr+"-1"                                  
                                            right_temp = right_temp + "["+str(expr)+"]"
                                        right=right_temp+right[right.index(")")+1:]
                                # conds.append(bexpr_parser.parse(str(left+op+right)))
                                else:
                                    if "(" in right:
                                        strs1=re.findall(r"[(](.*?)[)]", right)
                                        right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                                    else:
                                        right_exprs=list()
                                    exprs=longest_path[1]
                                    if exprs is not None and len(right_exprs) > 0:
                                        for  var in range(0,len(exprs)):
                                            hp_fun_onCon.append(hp_parser.parse(str(exprs[var])+":="+str(right_exprs[var])))
                                    return_var=longest_path[0]
                                    if return_var is not None:
                                        if isinstance(return_var,function.ListExpr):
                                            hp_fun_onCon.append(hp_parser.parse(str(return_var[0])+":= 0"))

                                            
                                        else:
                                            hp_fun_onCon.append(hp_parser.parse(str(return_var)+":= 0"))
                                           
                                    hp_fun_onCon.append(self.fun_dict[longest_path])

                                    

                                    if return_var is not None:
                                        if isinstance(return_var,function.ListExpr):
                                            hp_fun_onCon.append(hp_parser.parse(str(right[:right.index("(")]+"_"+str(return_var[0])+":="+str(return_var[0]))))
                                            right=str(right[:right.index("(")]+"_"+str(return_var[0]))
                                            # right = str(return_var[0])
                                            
                                        else:
                                            hp_fun_onCon.append(hp_parser.parse(str(right[:right.index("(")]+"_"+str(return_var)+":="+str(return_var))))
                                            right=str(right[:right.index("(")]+"_"+str(return_var))
                                            # right = str(return_var)
                                         



                        if re.match(pattern="^\\w+\\(\\w*(,\\w*)*\\)$", string=left) or re.match(pattern="^\\w+$",string=left):
                                longest_path=self.get_fun_by_path(str(left))
                                if longest_path is None:
                                    if "(" in left:
                                        strs1=re.findall(r"[(](.*?)[)]", left)
                                        left_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]                    
                                    else:
                                        left_exprs=list()
                                    if len(left_exprs) == 1:
                                        if left_exprs[0].isdigit():
                                                left_exprs[0]=int(left_exprs[0])-1
                                        else:
                                                left_exprs[0]=left_exprs[0]+"-1"
                                        left=left[:left.index("(")]+"["+str(left_exprs[0])+"]"+left[left.index(")")+1:]
                                    elif len(left_exprs) > 1:
                                        left_temp = left[:left.index("(")]
                                        for expr in left_exprs:
                                            if expr.isdigit():
                                                expr=int(expr)-1
                                            else:
                                                expr=expr+"-1"                                  
                                            left_temp = left_temp + "["+str(expr)+"]"
                                        left=left_temp+left[left.index(")")+1:]
                                # conds.append(bexpr_parser.parse(str(left+op+right)))
                                else:
                                    if "(" in left:
                                        strs1=re.findall(r"[(](.*?)[)]", left)
                                        left_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                                    else:
                                        left_exprs=list()
                                    exprs=longest_path[1]
                                    if exprs is not None and len(left_exprs) > 0:
                                        for  var in range(0,len(exprs)):
                                            hp_fun_onCon.append(hp_parser.parse(str(exprs[var])+":="+str(left_exprs[var])))
                                    return_var=longest_path[0]
                                    if return_var is not None:
                                        if isinstance(return_var,function.ListExpr):
                                            for  var in range(0,len(return_var)):
                                                hp_fun_onCon.append(hp_parser.parse(str(return_var[var])+":= 0"))
                                              
                                        else:
                                            hp_fun_onCon.append(hp_parser.parse(str(return_var)+":= 0"))
                                           
                                    hp_fun_onCon.append(self.fun_dict[longest_path])

                                    

                                    if return_var is not None:
                                        if isinstance(return_var,function.ListExpr):
                                            for  var in range(0,len(return_var)):
                                                hp_fun_onCon.append(hp_parser.parse(str(left[:left.index("(")]+"_"+str(return_var[var])+":="+str(return_var[var]))))
                                                left=str(left[:left.index("(")]+"_"+str(return_var[var]))
                                                # left =str(return_var[var])
                                                # conds.append(bexpr_parser.parse(str(return_var[var])+op+right))
                                        else:
                                            hp_fun_onCon.append(hp_parser.parse(str(left[:left.index("(")]+"_"+str(return_var)+":="+str(return_var))))
                                            left=str(left[:left.index("(")]+"_"+str(return_var))
                                            # left = str(return_var)
                        conds.append(bexpr_parser.parse(str(left+op+right)))                    # conds.append(bexpr_parser.parse(str(return_var)+op+right))

                        # else:
                        #     conds.append(bexpr_parser.parse(str(condition)))
                        #     continue
                        # if re.match(pattern="^\\w+\\(\\w*(,\\w*)*\\)$", string=right) or re.match(pattern="^\\w+$",string=right) :
                        #     longest_path=self.get_fun_by_path(str(right))
                        #     if longest_path is None:
                        #         if "(" in right:
                        #             strs1=re.findall(r"[(](.*?)[)]", right)
                        #             right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]                    
                        #         else:
                        #             right_exprs=list()
                        #         if len(right_exprs) == 1:
                        #             if right_exprs[0].isdigit():
                        #                     right_exprs[0]=int(right_exprs[0])-1
                        #             else:
                        #                     right_exprs[0]=right_exprs[0]+"-1"
                        #             right=right[:right.index("(")]+"["+str(right_exprs[0])+"]"+right[right.index(")")+1:]
                        #         elif len(right_exprs) > 1:
                        #             right_temp = right[:right.index("(")]
                        #             for expr in right_exprs:
                        #                 if expr.isdigit():
                        #                     expr=int(expr)-1
                        #                 else:
                        #                     expr=expr+"-1"                                  
                        #                 right_temp = right_temp + "["+str(expr)+"]"
                        #             right=right_temp+right[right.index(")")+1:]
                        #         conds.append(bexpr_parser.parse(str(left+op+right)))
                        #     else:
                        #         if "(" in right:
                        #             strs1=re.findall(r"[(](.*?)[)]", right)
                        #             right_exprs=list(strs1[0].split(",")) if  "," in strs1[0] else [strs1[0]]
                        #         else:
                        #             right_exprs=list()
                        #         exprs=longest_path[1]
                        #         if exprs is not None and len(right_exprs) > 0:
                        #             for  var in range(0,len(exprs)):
                        #                 hp_fun_onCon.append(hp_parser.parse(str(exprs[var])+":="+str(right_exprs[var])))
                        #         hp_fun_onCon.append(self.fun_dict[longest_path])

                        #         return_var=longest_path[0]

                        #         if return_var is not None and len(left) >0:
                        #             if isinstance(return_var,function.ListExpr):
                        #                 for  var in range(0,len(return_var)):
                        #                     conds.append(bexpr_parser.parse(left+op+str(return_var[var])))
                        #             else:
                        #                 conds.append(bexpr_parser.parse(str(return_var)+op+left))
                        
                    else:
                        try:
                            conds.append(bexpr_parser.parse(str(condition)))
                        except lark.exceptions.UnexpectedToken as e:
                            print("Parsing condition", condition)
                            raise e
            
            if "&&" in str(tran.condition):
                if len(conds_event) >0:
                    conds.extend(conds_event)
                conds.append(bexpr_parser.parse("done == 0"))
                cond = conj(*conds) if len(conds) >= 2 else conds[0]    
            elif "||" in str(tran.condition):
                if len(conds_event) >0:
                    cond_1=disj(*conds) if len(conds) >= 2 else conds[0]
                    cond=conj(cond_1,bexpr_parser.parse("done == 0"),*conds_event)
                else:
                    cond_1=disj(*conds) if len(conds) >= 2 else conds[0]
                    cond=conj(cond_1,bexpr_parser.parse("done == 0"))
            else:
                if len(conds_event) >0:
                    conds.extend(conds_event)
                conds.append(bexpr_parser.parse("done == 0"))
                cond = conj(*conds) if len(conds) >= 2 else conds[0] 
            dst_state = self.all_states[tran.dst]
            src_state = self.all_states[tran.src]
            current_tran_act_Q = list(tran_act_Q) + tran.tran_acts
            common_ancestor = get_common_ancestor(state, dst_state)
            assert common_ancestor == get_common_ancestor(dst_state, state)
            descendant_exit = list() if isinstance(state, Junction) else state.all_descendant_exit()
            exit_to_ancestor = state.exit_to(common_ancestor)
            enter_into_dst = common_ancestor.enter_into(dst_state)
            hps = list()
            hps1=list()
            hps2=list()
            if isinstance(dst_state, (AND_State, OR_State)):
                assert not isinstance(dst_state, AND_State) or tran_type == "inner_trans"
                if self.is_triggered_chart and self.trigger_type == "function-call":
                    hps=[hp_parser.parse('tri_event:=""')]
                    hps2=[hp_parser.parse('tri_event:=""')]
                hps=hps+tran.cond_acts + descendant_exit + exit_to_ancestor + current_tran_act_Q + enter_into_dst \
                      + [hp_parser.parse("done := 1")]
                hps2 =hps2+ tran.cond_acts + descendant_exit + exit_to_ancestor + current_tran_act_Q + enter_into_dst \
                      + [hp_parser.parse("done := 1")]
                final_cond=""
                for event in self.event_list:
                    if event.name == tran.event and ( event.trigger in ["EITHER_EDGE_EVENT","FALLING_EDGE_EVENT","RISING_EDGE_EVENT"] )and event.scope =="INPUT_EVENT":
                        
                        if event.trigger == "RISING_EDGE_EVENT":
                            conds2=list()
                            conds2.append(bexpr_parser.parse("osig"+str(event.port)+" <= 0"))
                            conds2.append(bexpr_parser.parse("out_tri"+str(event.port)+" > 0"))
                            cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                            conds1=list()
                            conds1.append(bexpr_parser.parse("osig"+str(event.port)+" < 0"))
                            conds1.append(bexpr_parser.parse("out_tri"+str(event.port)+" >= 0"))
                            cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                            final_cond=disj(cond2,cond1)
                        elif event.trigger == "FALLING_EDGE_EVENT":
                            conds=list()
                            conds.append(bexpr_parser.parse("osig"+str(event.port)+" >= 0"))
                            conds.append(bexpr_parser.parse("out_tri"+str(event.port)+" < 0"))
                            cond= conj(*conds) if len(conds) >= 2 else conds[0]
                            conds1=list()
                            conds1.append(bexpr_parser.parse("osig"+str(event.port)+" > 0"))
                            conds1.append(bexpr_parser.parse("out_tri"+str(event.port)+" <= 0"))
                            cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                            final_cond=disj(cond,cond1)
                        else:
                            conds=list()
                            conds.append(bexpr_parser.parse("osig"+str(event.port)+"!=out_tri"+str(event.port)))
                           
                            final_cond= conj(*conds) if len(conds) >= 2 else conds[0]
                        
                        hps=[ hp.Sequence( hp.Condition(final_cond,
                                          get_hcsp(hps2,self)))]

            elif isinstance(dst_state, Junction):
                if not dst_state.visited:  # has not been visited in this round
                    dst_state.visited = True
                    hp_list=list()
                    assert isinstance(dst_state.processes, list)
                    num = len(dst_state.processes)
                    process_name = dst_state.name+str(num)
                    #dst_state.visited = False      #？？？  hps中为什莫还包括exit_to_ancestor状态退出（当转换不是有效转换的话，状态应保持活动状态）
                    hps1 =tran.cond_acts + descendant_exit + exit_to_ancestor + current_tran_act_Q \
                          + enter_into_dst
                    #assert isinstance(process, (hp.Skip, hp.Condition, hp.ITE))
                      #？？？？
                    hp_list.append((cond, get_hcsp(hps1,self)))
                    # if len(conds) > 1:
                        
                    process=hp.ITE(hp_list, hp.Skip())
                    dst_state.processes.append((process_name,process ))
                    # else:
                    #     dst_state.processes.append((process_name,hp.Sequence(*hp_list)))
                    # hps = hps+tran.cond_acts + descendant_exit + exit_to_ancestor + current_tran_act_Q \
                    #        + enter_into_dst + ( [hp.Var(process_name)])
                    process1,hp_fun_onCon1=self.execute_trans_from_state(state=dst_state, tran_type="out_trans",
                                                             tran_act_Q=current_tran_act_Q)
                    # assert all(process_name != name for name, _ in dst_state.processes)
                    #self.execute_trans_from_state(state=dst_state, tran_type="out_trans",
                     #                                        tran_act_Q=current_tran_act_Q)
                    
                    # assert isinstance(process, (hp.Skip, hp.Condition, hp.ITE))
                    # dst_state.processes.append((process_name,hp.Sequence(get_hcsp([hp_fun_onCon1],self),process)))
                    dst_state.visited = False      #？？？  hps中为什莫还包括exit_to_ancestor状态退出（当转换不是有效转换的话，状态应保持活动状态）
                    hps =tran.cond_acts + descendant_exit + exit_to_ancestor + current_tran_act_Q \
                            + enter_into_dst +[hp_fun_onCon1] +( [process1])
                else:  # visited in this round
                    hps1 = hps+tran.cond_acts + descendant_exit + exit_to_ancestor + current_tran_act_Q \
                              + enter_into_dst 
                    hp_list=list()
                    hp_list.append((cond, get_hcsp(hps1,self)))
                    num1=0
                    num = len(dst_state.processes)
                    
                    for process in dst_state.processes:
                        if process[1] == hp.ITE(hp_list, hp.Skip()):
                            num1=num1+1
                    if num1 ==0:
                        process_name = dst_state.name+str(num)
                        dst_state.processes.append((process_name,hp.ITE(hp_list, hp.Skip()) ))
                    process_name = dst_state.processes[-1][1]
                    dst_trans=dst_state.out_trans
                    hp_loop_local=get_loop_hps(dst_state,dst_trans)
                    # process_name1 = dst_state.processes[-1][0]
                    cond_exs=conds
                    for tran in dst_trans:
                        dst_state1 = self.all_states[tran.dst]
                        if dst_state1.visited:
                            if dst_state1 == dst_state:
                                # process_name = dst_state.processes[-1][0]
                                # hp_loop.append(hp.Var(process_name))
                                break
                            else:
                                cond_exs.append(tran.condition)
                    cond_ex= conj(*cond_exs) if len(cond_exs) >= 2 else cond_exs[0]
                    hps =  [hp.Sequence(process_name,hp.Loop(hp.ITE(hp_loop_local,hp.Skip()),cond_ex))]
                   
                    
            # if len(mesg_hp)>=1:
            #     if_hps.append(hp.Sequence(mesg_hp,cond, get_hcsp(hps)))
            if_hps.append((cond, get_hcsp(hps,self))) #？？？？
        if len(if_hps) >= 1:
            return hp.ITE(if_hps, else_hp),get_hcsp(hp_fun_onCon,self)


        assert if_hps == list()
        
        return hp.Skip(),get_hcsp(hp_fun_onCon,self)

    def get_monitor_process(self):
        # Get the number of AND_states
        assert len(self.diagram.children) >= 1
        state_num = len(self.diagram.children) if isinstance(self.diagram.children[0], AND_State) else 1

        # Get input channels
        in_channels = []
        for port_id, in_var in self.port_to_in_var.items():
            line = self.dest_lines[port_id]
            ch_name = "ch_" + line.name + "_" + str(line.branch)
            in_channels.append(ch_name + "?" + in_var)
        in_channels.sort()

        # Get output channels
        out_channels = []
        for port_id, out_var in self.port_to_out_var.items():
            lines = self.src_lines[port_id]
            for line in lines:
                ch_name = "ch_" + line.name + "_" + str(line.branch)
                out_channels.append(ch_name + "!" + out_var)
        out_channels.sort()
        # Get VOut
        def vout(_i, _vars):
            if not _vars:
                return "skip"
            for state in self.all_states.values():
                if "a_"+state.name in _vars:
                    _vars.remove("a_"+state.name)
            if "done" in _vars:
                _vars.remove("done")
            if "E" in _vars:
                _vars.remove("E")
            return "; ".join("VOut" + str(_i) + "_" + _var + "!" + _var for _var in sorted(list(_vars)))

        def DBvout(_i, _vars):
            if not _vars:
                return "skip"
            for state in self.all_states.values():
                if "a_"+state.name in _vars:
                    _vars.remove("a_"+state.name) 
            if "done" in _vars:
                _vars.remove("done")  
            if "E" in _vars:
                _vars.remove("E") 
            return "; ".join("DBVOut" + str(_i) + "_" + _var + "!" + _var for _var in sorted(list(_vars)))

        # Get VIn
        def vin(_i, _vars):
            if not _vars:
                return "skip"
            for state in self.all_states.values():
                if "a_"+state.name in _vars:
                    _vars.remove("a_"+state.name)
            if "done" in _vars:
                _vars.remove("done")
            if "E" in _vars:
                _vars.remove("E")
            return "; ".join("VIn" + str(_i) + "_" + _var + "?" + _var for _var in sorted(list(_vars)))
        def DBvin(_i, _vars):
            if not _vars:
                return "skip"
            for state in self.all_states.values():
                if "a_"+state.name in _vars:
                    _vars.remove("a_"+state.name)
            if "done" in _vars:
                _vars.remove("done")
            if "E" in _vars:
                _vars.remove("E")
            return "; ".join("DBVIn" + str(_i) + "_" + _var + "?" + _var for _var in sorted(list(_vars)))
        # Variable Initialisation    num为当前并发进程的序号
        # init_vars = [hp.Assign(var_name, AConst(value)) for var_name, value in sorted(self.data.items())]
        if self.st == -1 or self.st == 0:
            self.st=0.1
        init_vars=[hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])) ] 
        init_vars.append(hp.Assign("num", AConst(0)))
        init_vars = hp.Sequence(*init_vars) if len(init_vars) >= 2 else init_vars[0]
        # Initial input and output channels, and delay
        init_ch = hp_parser.parse("; ".join(in_channels + out_channels + ["wait(" + str(self.st) + ")"]))
        # Get M process
        hp_M = hp.Sequence(init_vars, init_ch, hp.Loop(hp.Var("M_main")))

        

        in_channels = "; ".join(in_channels) + "; " if in_channels else ""
        out_channels = "; ".join(out_channels) + "; " if out_channels else ""

        # Get M_main process      BC为当前的广播事件的通道，BR为新的事件的广播申请，BO为广播结束
        hp_M_main = hp_parser.parse("num == 0 -> (" + in_channels + 'state :="" ; E := ""; EL := [""]; NL := [1]; num := 1)')
        for i in range(1, state_num + 1):
            i = str(i)
            s_i = self.get_state_by_name("S" + i)
            assert isinstance(s_i, AND_State)
            # vars_in_s_i = s_i.get_vars().union(set(self.port_to_in_var.values()))
            vars_in_s_i = set([var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]]).union(set(self.port_to_in_var.values()))
            hp_M_main = hp.Sequence(hp_M_main,
                                    hp_parser.parse("num == " + i + " -> (DState"+i+" ! state-->skip $ DBC" + i + "!E -->" + DBvout(i, vars_in_s_i)+" $ BC" + i + "!E --> " + vout(i, vars_in_s_i)
                                                    + " $ BR" + i + "?E -->" + vin(i, vars_in_s_i) +
                                                    "; EL := push(EL, E); NL := push(NL, 1); num := 1 $ DBR" + i + "?E -->"+ DBvin(i, vars_in_s_i) +";DBnum"+i+"?Dnum; num :=Dnum"+";DState"+i+"?state  $ DBO"+ i +"? -->"+ DBvin(i, vars_in_s_i)+
                                                ";num :=num+1 $ BO" + i + "? --> " + vin(i, vars_in_s_i) + "; num := num+1; NL := pop(NL); NL := push(NL, num))"))
        hp_M_main = hp.Sequence(hp_M_main,
                                hp_parser.parse("num == " + str(state_num + 1) +" -> (EL := pop(EL); NL := pop(NL);EL == [] -> (num := 0; "+ out_channels + "wait(" + str(self.st) + ")); EL != [] -> (E := top(EL); num := top(NL)))"))
        return hp_M, hp_M_main, state_num

    def get_process(self, event_var="E"):
        
        def get_S_du_and_P_diag(_state, _hps):
            _s_du = list()
            _p_diag = list()
            _p_diag_name = "Diag_" + _state.whole_name

            # if _state.du:  # add during action
            #     _s_du.extend(_state.du)
            # if isinstance(_state, OR_State) and _state.has_aux_var("state_time"):
            #     _s_du.append(hp_parser.parse("state_time := state_time+" + str(self.st)))
            if isinstance(_state, (AND_State, OR_State)) and not all(not isinstance(_child, (AND_State, OR_State)) for _child in _state.children):
                _s_du.append(hp.Var(_p_diag_name))  # P_diag

                if isinstance(_state.children[0], AND_State):
                    _p_diag = [hp.Var(_child.whole_name) for _child in _state.children]
                else:  # OR_State
                    _p_diag = [(_child.activated(), hp.Var(_child.whole_name))
                               for _child in _state.children if isinstance(_child, OR_State)]
            if len(_s_du) == 0:
                _s_du = hp.Skip()
            elif len(_s_du) == 1:
                _s_du = _s_du[0]
            else:
                _s_du = hp.Sequence(*_s_du)
            # _s_du = dur; P_diag

            # _hps is TTN(...)
            if isinstance(_state, (AND_State, OR_State)):
                if _hps != hp.Skip():  # generated from an OR-state
                    init = hp_parser.parse("done := 0")
                    _s_du = hp.Sequence(init, _hps) if _s_du == hp.Skip() \
                        else hp.Sequence(init, _hps, hp.Condition(cond=bexpr_parser.parse("done == 0"), hp=_s_du))
                # _s_du = done := False; TTN(...); \neg done -> (P_diag)
            return _s_du, _p_diag, _p_diag_name

        # Analyse P_diag recursively
        def analyse_P_diag(_p_diag, _processes): 
            for proc in _p_diag:
                # _state_name = proc.hp.name if isinstance(proc, hp.Condition) else proc.name
                _state_name = proc.name if isinstance(proc, hp.Var) else proc[1].name
                assert _state_name
                _state = self.get_state_by_whole_name(name=_state_name)
                _s_du, new_p_diag, new_p_diag_name = get_S_du_and_P_diag(_state=_state,
                                                                         _hps=self.execute_one_step_from_state(_state))
                _processes.add(_state_name, _s_du)
                if new_p_diag:
                    if isinstance(new_p_diag[0], hp.Var):
                        assert all(isinstance(e, hp.Var) for e in new_p_diag)
                        new_p_diag_proc = hp.Sequence(*new_p_diag) if len(new_p_diag) >= 2 else new_p_diag[0]
                    else:
                        assert all(isinstance(e, tuple) and len(e) == 2 for e in new_p_diag)
                        new_p_diag_proc = hp.ITE(if_hps=new_p_diag, else_hp=hp.Skip()) if len(new_p_diag) >= 2 \
                            else hp.Condition(cond=new_p_diag[0][0], hp=new_p_diag[0][1])
                    assert new_p_diag_name
                    _processes.add(new_p_diag_name, new_p_diag_proc)
                    analyse_P_diag(new_p_diag, _processes)

        # Get VOut
        def vout(_i, _vars):
            if not _vars:
                return "skip"
            for state in self.all_states.values():
                if "a_"+state.name in _vars:
                    _vars.remove("a_"+state.name)
            if "done" in _vars:
                _vars.remove("done")
            if "E" in _vars:
                _vars.remove("E")
            return "; ".join("VOut" + str(_i) + "_" + _var + "?" + _var for _var in sorted(list(_vars)))

        # Get VIn
        def vin(_i, _vars):
            if not _vars:
                return "skip"
            for state in self.all_states.values():
                if "a_"+state.name in _vars:
                    _vars.remove("a_"+state.name)
            if "done" in _vars:
                _vars.remove("done")
            if "E" in _vars:
                _vars.remove("E")
            return "; ".join("VIn" + str(_i) + "_" + _var + "!" + _var for _var in sorted(list(_vars)))
##########
        # Add VIn! after BR! in an hcsp list of state
        def add_VIn_after_BR_in_list(_num, _hps, _modified_vars):
            _vin = vin(_num, _modified_vars)
            if _vin == "skip":
                return _hps
            _vin = hp_parser.parse(_vin)
            assert isinstance(_vin, (hp.Sequence, hp.OutputChannel))

            new_hps = list()
            for sub_hp in _hps:
                #assert isinstance(sub_hp, hp.HCSP)
                if isinstance(sub_hp, hp.Sequence):
                    new_hps.extend(sub_hp.hps)
                else:
                    assert not isinstance(sub_hp, hp.Parallel)
                    new_hps.append(sub_hp)
                    if isinstance(sub_hp, hp.OutputChannel) and sub_hp.ch_name.name.startswith("BR"):
                        assert sub_hp.ch_name.name == "BR" + str(_num)
            assert len([sub_hp for sub_hp in _hps  # at least one BR!
                        if isinstance(sub_hp, hp.OutputChannel) and sub_hp.ch_name.name.startswith("BR")]) <= 1

            index_BR = None
            for _i in range(len(new_hps)):
                sub_hp = new_hps[_i]
                if isinstance(sub_hp, hp.OutputChannel) and sub_hp.ch_name.name.startswith("BR"):
                    index_BR = _i
                    break
            if index_BR:
                new_hps.insert(index_BR + 1, _vin)
            return new_hps

        # Add VIn! after BR! in given state
        def add_VIn_after_BR_in_state(_num, _state, _modified_vars):
            if isinstance(_state, (AND_State, OR_State)):
                if _state.en:
                    _state.en = add_VIn_after_BR_in_list(_num, _state.en, _modified_vars)
                if _state.du:
                    _state.du = add_VIn_after_BR_in_list(_num, _state.du, _modified_vars)
                if _state.ex:
                    _state.ex = add_VIn_after_BR_in_list(_num, _state.ex, _modified_vars)
                for tran in _state.inner_trans:
                    tran.cond_acts = add_VIn_after_BR_in_list(_num, tran.cond_acts, _modified_vars)
                    tran.tran_acts = add_VIn_after_BR_in_list(_num, tran.tran_acts, _modified_vars)
                if isinstance(_state, OR_State):
                    for tran in _state.out_trans:
                        tran.cond_acts = add_VIn_after_BR_in_list(_num, tran.cond_acts, _modified_vars)
                        tran.tran_acts = add_VIn_after_BR_in_list(_num, tran.tran_acts, _modified_vars)
                    if _state.default_tran:
                        _state.default_tran.cond_acts = add_VIn_after_BR_in_list(_num, _state.default_tran.cond_acts,
                                                                                 _modified_vars)
                        _state.default_tran.tran_acts = add_VIn_after_BR_in_list(_num, _state.default_tran.tran_acts,
                                                                                 _modified_vars)
                for _child in _state.children:
                    add_VIn_after_BR_in_state(_num, _child, _modified_vars)
            elif isinstance(_state, Junction):
                for tran in _state.out_trans:
                    tran.cond_acts = add_VIn_after_BR_in_list(_num, tran.cond_acts, _modified_vars)
                    tran.tran_acts = add_VIn_after_BR_in_list(_num, tran.tran_acts, _modified_vars)
                if _state.default_tran:
                        _state.default_tran.cond_acts = add_VIn_after_BR_in_list(_num, _state.default_tran.cond_acts,
                                                                                 _modified_vars)
                        _state.default_tran.tran_acts = add_VIn_after_BR_in_list(_num, _state.default_tran.tran_acts,
                                                                                _modified_vars)
                       
        # If there is no event, return two functions and move to get_pure_process()
        if not self.has_event:
            return get_S_du_and_P_diag, analyse_P_diag

        # List of HCSP processes
        processes = hp.HCSPProcess()
        # M and M_main
        hp_M, hp_M_main, state_num = self.get_monitor_process()
        processes.add("M", hp_M)
        processes.add("M_main", hp_M_main)

        # Get D process (system process)
        process = hp.Var("M")
        for num in range(state_num):
            process = hp.Parallel(process, hp.Var("S" + str(num + 1)))
        processes.insert(0, "D", process)
        if self.st == -1 or self.st == 0:
            self.st= 0.1
        # Get each S_i process
        parallel_states = self.diagram.children if self.diagram.name == "S0" else [self.diagram]
        assert len(parallel_states) == state_num
        state_root=""
        cond_exit=""
        state_root=parallel_states[0].root
        exit_states=list()
        for child in state_root.children:
            if isinstance(child,(AND_State,OR_State)):
                exit_states.append(child.exited()) 
        if len(exit_states)>0:
            cond_exit=conj(*exit_states) if len(exit_states) >= 2 else exit_states[0]
        else:
            cond_exit=bexpr_parser.parse('"true"'+' =="true"')
        i = 1
        for s_i in parallel_states:  # for each S_i state
            assert s_i.name == "S" + str(i)

            # vars_in_s_i = s_i.get_vars().union(set(self.port_to_in_var.values()))
            vars_in_s_i=set([var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]]).union(set(self.port_to_in_var.values()))
            add_VIn_after_BR_in_state(i, s_i, vars_in_s_i)

            s_du, p_diag, p_diag_name = get_S_du_and_P_diag(_state=s_i, _hps=self.execute_one_step_from_state(s_i))
            assert isinstance(s_du, hp.HCSP) and isinstance(p_diag, list)
            assert all(isinstance(s, (hp.Var, tuple)) for s in p_diag)
            # Body of process S_i
            if  s_i.name == "S" +str(self.dest_state_root_num):
                s_i_proc = hp.Sequence(hp_parser.parse("DState"+str(i)+"?state"+";BC" + str(i) + "?" + event_var + "; " + vout(i, vars_in_s_i)),
                                       s_du,  # S_du
                                       hp_parser.parse("BO" + str(i) + "!; " + vin(i, vars_in_s_i)))
            else:
                s_i_proc = hp.Sequence(hp_parser.parse("BC" + str(i) + "?" + event_var + "; " + vout(i, vars_in_s_i)),
                                       s_du,  # S_du
                                       hp_parser.parse("BO" + str(i) + "!; " + vin(i, vars_in_s_i)))
            # P_diag = p_diag_proc
            if p_diag:
                if isinstance(p_diag[0], hp.Var):
                    assert all(isinstance(e, hp.Var) for e in p_diag)
                    p_diag_proc = hp.Sequence(*p_diag) if len(p_diag) >= 2 else p_diag[0]
                else:
                    assert all(isinstance(e, tuple) and len(e) == 2 for e in p_diag)
                    p_diag_proc = hp.ITE(if_hps=p_diag, else_hp=hp.Skip()) if len(p_diag) >= 2 \
                        else hp.Condition(cond=p_diag[0][0], hp=p_diag[0][1])
                assert p_diag_name
                processes.add(p_diag_name, p_diag_proc)
                analyse_P_diag(p_diag, processes)  # analyse P_diag recursively

            # Check if there is an X in the processes
            # If so, then there is an event triggered inner the states,
            # which means process S_i is recursive.
            init_vars = [hp.Assign(var_name, AConst(value.value)) for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]]
            for s in self.all_states.values():
                if isinstance(s,OR_State) and s.has_aux_var("state_time"+str(s.ssid)):
                    init_vars.append(hp_parser.parse("state_time"+str(s.ssid)+" := 0"))
            # init_vars.append(hp_parser.parse("state_time := 0"))
            contain_X = False
            for _, process in processes.hps:
                # if hp.Var("X") in hp.decompose(process):
                if process.contain_hp(name="X"):
                    contain_X = True
                    if not self.is_triggered_chart :
                        s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self), get_hcsp(s_i.activate(),self),hp.Wait(AConst(self.st)),*self.add_state_time(),
                                           hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])),hp.Loop(hp.Sequence(hp.Recursion(s_i_proc),hp.Wait(AConst(self.st)),*self.add_state_time())))
                    else:
                        if self.trigger_type == "function-call":
                            # conds=list()
                            # conds.append(bexpr_parser.parse( "tri_event" +'!=""'))
                            # cond = conj(*conds) if len(conds) >= 2 else conds[0] 
                            # s_i_proc = hp.Sequence(get_hcsp(s_i.init()),hp.Loop(hp.Sequence(hp_parser.parse('tri_event := ""'),hp_parser.parse("tri?tri_event "),hp.Condition(cond,hp.Sequence(get_hcsp(s_i.activate()),hp.Recursion(s_i_proc))
                            #                    ))))
                            conds=list()
                            conds.append(bexpr_parser.parse( "tri_event" +'!=""'))
                            cond = conj(*conds) if len(conds) >= 2 else conds[0] 
                            s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),hp.Loop(hp.Sequence(hp_parser.parse('tri_event := ""'),hp_parser.parse("tri"+"?tri_event"),hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(get_hcsp(s_i.activate(),self),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)))),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])), hp.Recursion(s_i_proc),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)) )),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                        elif self.trigger_type == "rising":
                            # conds=list()
                            # conds.append(bexpr_parser.parse("osig <= 0"))
                            # conds.append(bexpr_parser.parse("out_tri > 0"))
                            # cond= conj(*conds) if len(conds) >= 2 else conds[0]
                            # conds1=list()
                            # conds1.append(bexpr_parser.parse("osig < 0"))
                            # conds1.append(bexpr_parser.parse("out_tri >= 0"))
                            # cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                            # final_cond=disj(cond,cond1)
                            # s_i_proc = hp.Sequence(get_hcsp(s_i.init()),hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"),hp.Condition(final_cond,hp.Sequence(get_hcsp(s_i.activate()),hp.Recursion(s_i_proc))
                            #                   ),hp_parser.parse("osig:=out_tri"))))
                            flag=0
                            has_mux_hps_init=list()
                            has_mux_hps=list()
                            has_mux_cond=list()
                            has_mux_end=list()
                            for event in self.event_list:
                                if (event.trigger in ["EITHER_EDGE_EVENT","FALLING_EDGE_EVENT","RISING_EDGE_EVENT"] )and event.scope =="INPUT_EVENT":
                                    cond2=""
                                    cond1=""
                                    final_cond=""
                                    flag+=1
                                    has_mux_hps_init.append(hp_parser.parse("ch_trig"+str(event.port)+"?osig"+str(event.port)))
                                    has_mux_hps.append(hp_parser.parse("ch_trig"+str(event.port)+"?out_tri"+str(event.port)))
                                    conds=list()
                                    conds.append(bexpr_parser.parse("osig"+str(event.port)+" <= 0"))
                                    conds.append(bexpr_parser.parse("out_tri"+str(event.port)+" > 0"))
                                    cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                                    conds1=list()
                                    conds1.append(bexpr_parser.parse("osig"+str(event.port)+" < 0"))
                                    conds1.append(bexpr_parser.parse("out_tri"+str(event.port)+" >= 0"))
                                    cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                                    final_cond=disj(cond2,cond1)
                                    has_mux_cond.append(final_cond)
                                    has_mux_end.append(hp_parser.parse("osig"+str(event.port)+":=out_tri"+str(event.port)))
                            cond=disj(*has_mux_cond) if len(has_mux_cond) >= 2 else has_mux_cond[0]
                            if flag>0 and flag == 1:
                                cond2=""
                                cond1=""
                                conds=list()
                                conds.append(bexpr_parser.parse("osig <= 0"))
                                conds.append(bexpr_parser.parse("out_tri > 0"))
                                cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                                conds1=list()
                                conds1.append(bexpr_parser.parse("osig < 0"))
                                conds1.append(bexpr_parser.parse("out_tri >= 0"))
                                cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                                final_cond=disj(cond2,cond1)
                                s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"),hp.Condition(final_cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence( get_hcsp(s_i.activate(),self),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp_parser.parse("ch_trig"+"?out_tri"))),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])),hp.Recursion(s_i_proc))),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                            elif flag > 1:
                                s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),*has_mux_hps_init,hp.Loop(hp.Sequence(*has_mux_hps, hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(get_hcsp(s_i.activate(),self),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),*has_mux_hps)),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])), hp.Recursion(s_i_proc))),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                        elif self.trigger_type == "falling":
                            # conds=list()
                            # conds.append(bexpr_parser.parse("osig >= 0"))
                            # conds.append(bexpr_parser.parse("out_tri < 0"))
                            # cond= conj(*conds) if len(conds) >= 2 else conds[0]
                            # conds1=list()
                            # conds1.append(bexpr_parser.parse("osig > 0"))
                            # conds1.append(bexpr_parser.parse("out_tri <= 0"))
                            # cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                            # final_cond=disj(cond,cond1)
                            # s_i_proc = hp.Sequence(get_hcsp(s_i.init()),hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"),hp.Condition(final_cond,hp.Sequence(get_hcsp(s_i.activate()),hp.Recursion(s_i_proc))
                            #                    ),hp_parser.parse("osig:=out_tri"))))
                            flag=0
                            has_mux_hps_init=list()
                            has_mux_hps=list()
                            has_mux_cond=list()
                            has_mux_end=list()
                            for event in self.event_list:
                                if (event.trigger in ["EITHER_EDGE_EVENT","FALLING_EDGE_EVENT","RISING_EDGE_EVENT"] )and event.scope =="INPUT_EVENT":
                                    cond2=""
                                    cond1=""
                                    final_cond=""
                                    flag+=1
                                    has_mux_hps_init.append(hp_parser.parse("ch_trig"+str(event.port)+"?osig"+str(event.port)))
                                    has_mux_hps.append(hp_parser.parse("ch_trig"+str(event.port)+"?out_tri"+str(event.port)))
                                    conds=list()
                                    conds.append(bexpr_parser.parse("osig"+str(event.port)+" > 0"))
                                    conds.append(bexpr_parser.parse("out_tri"+str(event.port)+" <= 0"))
                                    cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                                    conds1=list()
                                    conds1.append(bexpr_parser.parse("osig"+str(event.port)+" >= 0"))
                                    conds1.append(bexpr_parser.parse("out_tri"+str(event.port)+" < 0"))
                                    cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                                    final_cond=disj(cond2,cond1)
                                    has_mux_cond.append(final_cond)
                                    has_mux_end.append(hp_parser.parse("osig"+str(event.port)+":=out_tri"+str(event.port)))
                            cond=disj(*has_mux_cond) if len(has_mux_cond) >= 2 else has_mux_cond[0]
                            if flag>0 and flag == 1:
                                cond2=""
                                cond1=""
                                conds=list()
                                conds.append(bexpr_parser.parse("osig > 0"))
                                conds.append(bexpr_parser.parse("out_tri <= 0"))
                                cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                                conds1=list()
                                conds1.append(bexpr_parser.parse("osig >= 0"))
                                conds1.append(bexpr_parser.parse("out_tri < 0"))
                                cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                                final_cond=disj(cond2,cond1)
                                s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"),hp.Condition(final_cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence( get_hcsp(s_i.activate(),self),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),hp_parser.parse("ch_trig"+"?out_tri"))),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])),hp.Recursion(s_i_proc))),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                            elif flag > 1:
                                s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),*has_mux_hps_init,hp.Loop(hp.Sequence(*has_mux_hps, hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(get_hcsp(s_i.activate(),self),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),*has_mux_hps)),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])), hp.Recursion(s_i_proc))),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                        else:
                            # s_i_proc = hp.Sequence(get_hcsp(s_i.init()),hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"),hp.Condition(bexpr_parser.parse("osig!=out_tri"),hp.Sequence(get_hcsp(s_i.activate()),hp.Recursion(s_i_proc))
                            #                    ),hp_parser.parse("osig:=out_tri"))))

                            #######
                            flag=0
                            has_mux_hps_init=list()
                            has_mux_hps=list()
                            has_mux_cond=list()
                            has_mux_end=list()
                            for event in self.event_list:
                                if (event.trigger in ["EITHER_EDGE_EVENT","FALLING_EDGE_EVENT","RISING_EDGE_EVENT"] )and event.scope =="INPUT_EVENT":
                                    flag+=1
                                    has_mux_hps_init.append(hp_parser.parse("ch_trig"+str(event.port)+"?osig"+str(event.port)))
                                    has_mux_hps.append(hp_parser.parse("ch_trig"+str(event.port)+"?out_tri"+str(event.port)))
                                    has_mux_cond.append(bexpr_parser.parse("osig"+str(event.port)+"!=out_tri"+str(event.port)))
                                    has_mux_end.append(hp_parser.parse("osig"+str(event.port)+":=out_tri"+str(event.port)))
                            cond=disj(*has_mux_cond) if len(has_mux_cond) >= 2 else has_mux_cond[0]
                            if flag>0 and flag == 1:
                                s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"),hp.Condition(bexpr_parser.parse("osig!=out_tri"),hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(get_hcsp(s_i.activate(),self),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp_parser.parse("ch_trig"+"?out_tri"))) ,hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])), hp.Recursion(s_i_proc)) ),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                            elif flag > 1:
                                s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),*has_mux_hps_init,hp.Loop(hp.Sequence(*has_mux_hps,hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(get_hcsp(s_i.activate(),self),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),*has_mux_hps)),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])), hp.Recursion(s_i_proc)) ),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                    break
            if not contain_X:
                if not self.is_triggered_chart :
                    s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self), get_hcsp(s_i.activate(),self),hp.Wait(AConst(self.st)),*self.add_state_time(),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])), hp.Loop(hp.Sequence(s_i_proc,hp.Wait(AConst(self.st)),*self.add_state_time())))
                
                else:
                    if self.trigger_type == "function-call":
                        conds=list()
                        conds.append(bexpr_parser.parse( "tri_event" +'!=""'))
                        cond = conj(*conds) if len(conds) >= 2 else conds[0] 
                        s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),hp.Loop(hp.Sequence(hp_parser.parse('tri_event := ""'),hp_parser.parse("tri"+"?tri_event"),hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(get_hcsp(s_i.activate(),self),hp.Wait(AConst(self.st)),*self.add_state_time())),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])), s_i_proc,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)) )),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                    elif self.trigger_type =="rising":
                        flag=0
                        has_mux_hps_init=list()
                        has_mux_hps=list()
                        has_mux_cond=list()
                        has_mux_end=list()
                        for event in self.event_list:
                            if (event.trigger in ["EITHER_EDGE_EVENT","FALLING_EDGE_EVENT","RISING_EDGE_EVENT"] )and event.scope =="INPUT_EVENT":
                                cond2=""
                                cond1=""
                                final_cond=""
                                flag+=1
                                has_mux_hps_init.append(hp_parser.parse("ch_trig"+str(event.port)+"?osig"+str(event.port)))
                                has_mux_hps.append(hp_parser.parse("ch_trig"+str(event.port)+"?out_tri"+str(event.port)))
                                conds=list()
                                conds.append(bexpr_parser.parse("osig"+str(event.port)+" <= 0"))
                                conds.append(bexpr_parser.parse("out_tri"+str(event.port)+" > 0"))
                                cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                                conds1=list()
                                conds1.append(bexpr_parser.parse("osig"+str(event.port)+" < 0"))
                                conds1.append(bexpr_parser.parse("out_tri"+str(event.port)+" >= 0"))
                                cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                                final_cond=disj(cond2,cond1)
                                has_mux_cond.append(final_cond)
                                has_mux_end.append(hp_parser.parse("osig"+str(event.port)+":=out_tri"+str(event.port)))
                        cond=disj(*has_mux_cond) if len(has_mux_cond) >= 2 else has_mux_cond[0]
                        if flag>0 and flag == 1:
                            cond2=""
                            cond1=""
                            conds=list()
                            conds.append(bexpr_parser.parse("osig <= 0"))
                            conds.append(bexpr_parser.parse("out_tri > 0"))
                            cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                            conds1=list()
                            conds1.append(bexpr_parser.parse("osig < 0"))
                            conds1.append(bexpr_parser.parse("out_tri >= 0"))
                            cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                            final_cond=disj(cond2,cond1)
                            s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"),hp.Condition(final_cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence( get_hcsp(s_i.activate(),self),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),hp_parser.parse("ch_trig"+"?out_tri"))),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])),s_i_proc)),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                        elif flag > 1:
                            s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),*has_mux_hps_init,hp.Loop(hp.Sequence(*has_mux_hps, hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(get_hcsp(s_i.activate(),self),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),*has_mux_hps)),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])), s_i_proc)),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                    
                    elif self.trigger_type == "falling":
                        flag=0
                        has_mux_hps_init=list()
                        has_mux_hps=list()
                        has_mux_cond=list()
                        has_mux_end=list()
                        for event in self.event_list:
                            if (event.trigger in ["EITHER_EDGE_EVENT","FALLING_EDGE_EVENT","RISING_EDGE_EVENT"] )and event.scope =="INPUT_EVENT":
                                cond2=""
                                cond1=""
                                final_cond=""
                                flag+=1
                                has_mux_hps_init.append(hp_parser.parse("ch_trig"+str(event.port)+"?osig"+str(event.port)))
                                has_mux_hps.append(hp_parser.parse("ch_trig"+str(event.port)+"?out_tri"+str(event.port)))
                                conds=list()
                                conds.append(bexpr_parser.parse("osig"+str(event.port)+" > 0"))
                                conds.append(bexpr_parser.parse("out_tri"+str(event.port)+" <= 0"))
                                cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                                conds1=list()
                                conds1.append(bexpr_parser.parse("osig"+str(event.port)+" >= 0"))
                                conds1.append(bexpr_parser.parse("out_tri"+str(event.port)+" < 0"))
                                cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                                final_cond=disj(cond2,cond1)
                                has_mux_cond.append(final_cond)
                                has_mux_end.append(hp_parser.parse("osig"+str(event.port)+":=out_tri"+str(event.port)))
                        cond=disj(*has_mux_cond) if len(has_mux_cond) >= 2 else has_mux_cond[0]
                        if flag>0 and flag == 1:
                            cond2=""
                            cond1=""
                            conds=list()
                            conds.append(bexpr_parser.parse("osig > 0"))
                            conds.append(bexpr_parser.parse("out_tri <= 0"))
                            cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                            conds1=list()
                            conds1.append(bexpr_parser.parse("osig >= 0"))
                            conds1.append(bexpr_parser.parse("out_tri < 0"))
                            cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                            final_cond=disj(cond2,cond1)
                            s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"),hp.Condition(final_cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence( get_hcsp(s_i.activate(),self),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),hp_parser.parse("ch_trig"+"?out_tri"))),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])),s_i_proc)),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                        elif flag > 1:
                            s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),*has_mux_hps_init,hp.Loop(hp.Sequence(*has_mux_hps, hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(get_hcsp(s_i.activate(),self),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),*has_mux_hps)),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])), s_i_proc)),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                    
                            
                    else:
                        flag=0
                        has_mux_hps_init=list()
                        has_mux_hps=list()
                        has_mux_cond=list()
                        has_mux_end=list()
                        for event in self.event_list:
                            if (event.trigger in ["EITHER_EDGE_EVENT","FALLING_EDGE_EVENT","RISING_EDGE_EVENT"] )and event.scope =="INPUT_EVENT":
                                flag+=1
                                has_mux_hps_init.append(hp_parser.parse("ch_trig"+str(event.port)+"?osig"+str(event.port)))
                                has_mux_hps.append(hp_parser.parse("ch_trig"+str(event.port)+"?out_tri"+str(event.port)))
                                has_mux_cond.append(bexpr_parser.parse("osig"+str(event.port)+"!=out_tri"+str(event.port)))
                                has_mux_end.append(hp_parser.parse("osig"+str(event.port)+":=out_tri"+str(event.port)))
                        cond=disj(*has_mux_cond) if len(has_mux_cond) >= 2 else has_mux_cond[0]
                        if flag>0 and flag == 1:
                            s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"),hp.Condition(bexpr_parser.parse("osig!=out_tri"),hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(get_hcsp(s_i.activate(),self),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp_parser.parse("ch_trig"+"?out_tri"))) ,hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])), s_i_proc) ),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                        elif flag > 1:
                            s_i_proc = hp.Sequence(*init_vars,get_hcsp(s_i.init(),self),*has_mux_hps_init,hp.Loop(hp.Sequence(*has_mux_hps,hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(get_hcsp(s_i.activate(),self),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),*has_mux_hps)),hp_parser.parse(vin(0,[var_name for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]])), s_i_proc) ),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                #s_i_proc = hp.Sequence(get_hcsp(s_i.init()), get_hcsp(s_i.activate()),s_i_proc)

            # The output order is after D, M and M_main
            processes.insert(3, s_i.name, s_i_proc)

            i += 1

        # Add Junction processes
        for state in self.all_states.values():
            if isinstance(state, Junction) and state.type != "HISTORY_JUNCTION":
                # assert state.processes

                for process_name, process in state.processes:
                    processes.add(process_name, process)
        substituted = processes.substitute()
        # Only one parallel process
        assert len([process for process in substituted.values() if isinstance(process, hp.Parallel)]) == 1

        new_processes = hp.HCSPProcess()
        for name, process in substituted.items():
            if isinstance(process, hp.Parallel):
                for _hp in process.hps:
                    assert isinstance(_hp, hp.Var)
                    new_processes.add(_hp.name, substituted[_hp.name])
                break

        return new_processes

    def get_pure_process(self):
        assert not self.has_event
        get_S_du_and_P_diag, analyse_P_diag = self.get_process()
        # Initialise variables
        init_vars = [hp.Assign(var_name, AConst(value.value)) for var_name, value in sorted(self.data.items())  if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]]
        for s in self.all_states.values():
                if isinstance(s,OR_State) and s.has_aux_var("state_time"+str(s.ssid)):
                    init_vars.append(hp_parser.parse("state_time"+str(s.ssid)+" := 0"))
        # init_vars.append(hp_parser.parse("state_time := 0"))
        # Initialise and Activate states
        init_states = []
        exit_states=[]
        activate_states = list()
        state_root=""
        cond_exit=""
        parallel_states = self.diagram.children if self.diagram.name == "S0" else [self.diagram]
        for s_i in parallel_states:
            init_states.extend(s_i.init())
            activate_states.extend(s_i.activate())
            
            state_root=s_i.root
    
        for child in state_root.children:
            if isinstance(child,(AND_State,OR_State)):
                exit_states.append(child.exited()) 
        if len(exit_states)>0:
            cond_exit=conj(*exit_states) if len(exit_states) >= 2 else exit_states[0]
        else:
            cond_exit=bexpr_parser.parse('"true"'+' =="true"')
        # for sub_hp in init_states + activate_states:
        #     #assert isinstance(sub_hp, (hp.Assign, hp.Sequence,hp.OutputChannel,hp.InputChannel))
        #     if isinstance(sub_hp, hp.Sequence):
        #         assert all(isinstance(_hp, hp.Assign) for _hp in sub_hp.hps)
        # Null channel operations at the first round
        in_chs = []
        for port_id, in_var in self.port_to_in_var.items():
            line = self.dest_lines[port_id]
            ch_name = "ch_" + line.name + "_" + str(line.branch)
            in_chs.append(hp_parser.parse(ch_name + "?" + in_var))
        out_chs = []
        for port_id, out_var in self.port_to_out_var.items():
            lines = self.src_lines[port_id]
            for line in lines:
                ch_name = "ch_" + line.name + "_" + str(line.branch)
                out_chs.append(hp_parser.parse(ch_name + "!" + out_var))

        # Initialzation of the process
        if not self.is_triggered_chart:
            init_hps = init_vars + init_states + activate_states + in_chs + out_chs
        else:
            init_hps = init_vars+init_states
        # Delay one period at the first round
        if self.st == -1 or self.st == 0:
            self.st=0.1
        init_vars = [hp.Assign(var_name, AConst(value.value)) for var_name, value in sorted(self.data.items()) if value.scope not in ['FUNCTION_OUTPUT_DATA',"FUNCTION_INPUT_DATA","DATA_STORE_MEMORY_DATA"]]
        init_hp = hp.Sequence(*init_hps, hp.Wait(AConst(self.st)),*self.add_state_time())
        
        # init_hp = hp.Sequence(*init_hps)
        processes = hp.HCSPProcess()
        # Get main process
        main_body = [hp.Var(state.name) for state in parallel_states]
        main_processes = in_chs + main_body + out_chs
        if not self.is_triggered_chart:
            main_process = hp.Sequence(init_hp, hp.Loop(hp.Sequence(*main_processes, hp.Wait(AConst(self.st)),*self.add_state_time())))
        else:
            if self.trigger_type == "function-call":
                conds=list()
                conds.append(bexpr_parser.parse( "tri_event" +'!=""'))
                cond = conj(*conds) if len(conds) >= 2 else conds[0]   
                main_process = hp.Sequence(init_hp,hp.Loop(hp.Sequence(hp_parser.parse('tri_event := ""'), hp_parser.parse("tri"+"?tri_event"),hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(*activate_states ,*in_chs )) , *out_chs,*main_processes)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
            elif self.trigger_type == "rising":
                flag=0
                has_mux_hps_init=list()
                has_mux_hps=list()
                has_mux_cond=list()
                has_mux_end=list()
                for event in self.event_list:
                    if (event.trigger in ["EITHER_EDGE_EVENT","FALLING_EDGE_EVENT","RISING_EDGE_EVENT"] )and event.scope =="INPUT_EVENT":
                        cond2=""
                        cond1=""
                        final_cond=""
                        flag+=1
                        has_mux_hps_init.append(hp_parser.parse("ch_trig"+str(event.port)+"?osig"+str(event.port)))
                        has_mux_hps.append(hp_parser.parse("ch_trig"+str(event.port)+"?out_tri"+str(event.port)))
                        conds=list()
                        conds.append(bexpr_parser.parse("osig"+str(event.port)+" <= 0"))
                        conds.append(bexpr_parser.parse("out_tri"+str(event.port)+" > 0"))
                        cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                        conds1=list()
                        conds1.append(bexpr_parser.parse("osig"+str(event.port)+" < 0"))
                        conds1.append(bexpr_parser.parse("out_tri"+str(event.port)+" >= 0"))
                        cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                        final_cond=disj(cond2,cond1)
                        has_mux_cond.append(final_cond)
                        has_mux_end.append(hp_parser.parse("osig"+str(event.port)+":=out_tri"+str(event.port)))
                cond=disj(*has_mux_cond) if len(has_mux_cond) >= 2 else has_mux_cond[0]
                if flag>0 and flag == 1:
                    cond2=""
                    cond1=""
                    conds=list()
                    conds.append(bexpr_parser.parse("osig <= 0"))
                    conds.append(bexpr_parser.parse("out_tri > 0"))
                    cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                    conds1=list()
                    conds1.append(bexpr_parser.parse("osig < 0"))
                    conds1.append(bexpr_parser.parse("out_tri >= 0"))
                    cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                    final_cond=disj(cond2,cond1)
                    main_process = hp.Sequence(init_hp,hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"), hp.Condition(final_cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(*activate_states ,*in_chs,hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp_parser.parse("ch_trig"+"?out_tri"))) , *out_chs,*main_processes)),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                elif flag > 1:
                    main_process = hp.Sequence(init_hp,*has_mux_hps_init,hp.Loop(hp.Sequence(*has_mux_hps, hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(*activate_states ,*in_chs ,*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),*has_mux_hps)), *out_chs,*main_processes)),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
            elif self.trigger_type == "falling":
                flag=0
                has_mux_hps_init=list()
                has_mux_hps=list()
                has_mux_cond=list()
                has_mux_end=list()
                for event in self.event_list:
                    if (event.trigger in ["EITHER_EDGE_EVENT","FALLING_EDGE_EVENT","RISING_EDGE_EVENT"] )and event.scope =="INPUT_EVENT":
                        cond2=""
                        cond1=""
                        final_cond=""
                        flag+=1
                        has_mux_hps_init.append(hp_parser.parse("ch_trig"+str(event.port)+"?osig"+str(event.port)))
                        has_mux_hps.append(hp_parser.parse("ch_trig"+str(event.port)+"?out_tri"+str(event.port)))
                        conds=list()
                        conds.append(bexpr_parser.parse("osig"+str(event.port)+" > 0"))
                        conds.append(bexpr_parser.parse("out_tri"+str(event.port)+" <= 0"))
                        cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                        conds1=list()
                        conds1.append(bexpr_parser.parse("osig"+str(event.port)+" >= 0"))
                        conds1.append(bexpr_parser.parse("out_tri"+str(event.port)+" < 0"))
                        cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                        final_cond=disj(cond2,cond1)
                        has_mux_cond.append(final_cond)
                        has_mux_end.append(hp_parser.parse("osig"+str(event.port)+":=out_tri"+str(event.port)))
                cond=disj(*has_mux_cond) if len(has_mux_cond) >= 2 else has_mux_cond[0]
                if flag>0 and flag == 1:
                    cond2=""
                    cond1=""
                    conds=list()
                    conds.append(bexpr_parser.parse("osig > 0"))
                    conds.append(bexpr_parser.parse("out_tri <= 0"))
                    cond2= conj(*conds) if len(conds) >= 2 else conds[0]
                    conds1=list()
                    conds1.append(bexpr_parser.parse("osig >= 0"))
                    conds1.append(bexpr_parser.parse("out_tri < 0"))
                    cond1=conj(*conds1) if len(conds1) >= 2 else conds1[0]
                    final_cond=disj(cond2,cond1)
                    main_process = hp.Sequence(init_hp,hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"), hp.Condition(final_cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(*activate_states ,*in_chs,hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),hp_parser.parse("ch_trig"+"?out_tri"))) , *out_chs,*main_processes)),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                elif flag > 1:
                    main_process = hp.Sequence(init_hp,*has_mux_hps_init,hp.Loop(hp.Sequence(*has_mux_hps, hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(*activate_states ,*in_chs ,*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),*has_mux_hps)), *out_chs,*main_processes)),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
            else:
                flag=0
                has_mux_hps_init=list()
                has_mux_hps=list()
                has_mux_cond=list()
                has_mux_end=list()
                for event in self.event_list:
                    if (event.trigger in ["EITHER_EDGE_EVENT","FALLING_EDGE_EVENT","RISING_EDGE_EVENT"] )and event.scope =="INPUT_EVENT":
                        flag+=1
                        has_mux_hps_init.append(hp_parser.parse("ch_trig"+str(event.port)+"?osig"+str(event.port)))
                        has_mux_hps.append(hp_parser.parse("ch_trig"+str(event.port)+"?out_tri"+str(event.port)))
                        has_mux_cond.append(bexpr_parser.parse("osig"+str(event.port)+"!=out_tri"+str(event.port)))
                        has_mux_end.append(hp_parser.parse("osig"+str(event.port)+":=out_tri"+str(event.port)))
                cond=disj(*has_mux_cond) if len(has_mux_cond) >= 2 else has_mux_cond[0]
                if flag>0 and flag == 1:
                   main_process = hp.Sequence(init_hp,hp_parser.parse("ch_trig"+"?osig"),hp.Loop(hp.Sequence(hp_parser.parse("ch_trig"+"?out_tri"), hp.Condition(bexpr_parser.parse("osig!=out_tri"),hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(*activate_states ,*in_chs,hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time +"+str(self.st)),hp_parser.parse("ch_trig"+"?out_tri") )), *out_chs,*main_processes)),hp_parser.parse("osig:=out_tri"),hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
                elif flag > 1:

                    main_process = hp.Sequence(init_hp,get_hcsp(has_mux_hps_init,self),hp.Loop(hp.Sequence(*has_mux_hps, hp.Condition(cond,hp.Sequence(hp.Condition(bexpr_parser.parse("a_"+state_root.name+"== 0"),hp.Sequence(*activate_states ,*in_chs ,*has_mux_end,hp.Wait(AConst(self.st)),*self.add_state_time(),*has_mux_hps)) , *out_chs,*main_processes)),*has_mux_end,hp.Wait(AConst(self.st)),hp_parser.parse("state_time := state_time+ "+str(self.st)),hp.Condition(cond_exit,hp_parser.parse("a_"+state_root.name+":= 0")))))
        processes.add(self.name, main_process)

        # Get each S_i process
        i = 0
        for s_i in parallel_states:  # for each S_i state
            i += 1
            assert s_i.name == "S" + str(i)
            # if isinstance (s_i.children[0],Junction):
            #     num = len(s_i.children[0].processes)
            #     process_name = s_i.children[0].name+str(num)
            #     s_i.children[0].processes.append((process_name, hp.Skip()))
            #     s_i.children[0].visited =True
            #     s_du =self.execute_one_step_from_state(s_i.children[0])
                
            #     processes.add(s_i.name, s_du)

            # else:

            s_du, p_diag, p_diag_name = get_S_du_and_P_diag(_state=s_i,
                                                        _hps=self.execute_one_step_from_state(s_i))
        
            assert isinstance(s_du, hp.HCSP) and isinstance(p_diag, list)
            assert all(isinstance(s, (hp.Var, tuple)) for s in p_diag)
            processes.add(s_i.name, s_du)

            # P_diag = p_diag_proc
            if p_diag:
                if isinstance(p_diag[0], hp.Var):
                    assert all(isinstance(e, hp.Var) for e in p_diag)
                    p_diag_proc = hp.Sequence(*p_diag) if len(p_diag) >= 2 else p_diag[0]
                else:
                    assert all(isinstance(e, tuple) and len(e) == 2 for e in p_diag)
                    p_diag_proc = hp.ITE(if_hps=p_diag, else_hp=hp.Skip()) if len(p_diag) >= 2 \
                        else hp.Condition(cond=p_diag[0][0], hp=p_diag[0][1])
                assert p_diag_name
                processes.add(p_diag_name, p_diag_proc)
                analyse_P_diag(p_diag, processes)  # analyse P_diag recursively
            

        # Add Junction processes
        for state in self.all_states.values():

            if isinstance(state, Junction) and state.type != "HISTORY_JUNCTION":
                #assert state.processes
                for process_name, process in state.processes:
                    processes.add(process_name, process)
        substituted = processes.substitute()
        processes.hps = [(self.name, substituted[self.name])]
        
        return processes
