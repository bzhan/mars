import re
import html
from ss2hcsp.sf.sf_parser.parser import condition_parser
from ss2hcsp.hcsp.parser import bexpr_parser
from ss2hcsp.hcsp.expr import BExpr
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.sf.sf_parser.cond_tran import Assign,ListExpr
from ss2hcsp.hcsp.hcsp import OutputChannel
from ss2hcsp.sf.sf_parser import parser
from ss2hcsp.sf.sf_parser.cond_tran import FunExpr

class Transition:
    def __init__(self, ssid, label, order=0, src="", dst=""):
        self.ssid = ssid
        self.label = label
        self.order = order
        self.src = src
        self.dst = dst
        self.root = None
        self.location = None  # in which state

        self.event = None
        self.message=None
        self.condition = None
        self.cond_acts = list()
        self.tran_acts = list()
        self.cond_vars = set()  # record SPECIAL (e.g., state time) variables in the condition

        self.parse()

    def __str__(self):
        if self.label:
            return "(%s)--%s-->(%s)" % (self.src, self.label, self.dst)
        else:
            return "(%s)--->(%s)" % (self.src, self.dst)

    def __repr__(self):
        return "Transition(%s, %s, %s, %s, %s)" % \
               (self.ssid, self.label, self.order, self.src, self.dst)

    def parse(self):
        if self.label is not None:
            func = parser.transition_parser.parse(html.unescape(self.label))
            if func.cond:

                if isinstance(func.cond,FunExpr):
                    if func.cond.fun_name == "after":
                        number, event = str(func.cond.exprs[0]),str(func.cond.exprs[1])
                        if event == "sec":
                            special_var = "state_time"+str(self.src)
                            self.condition = bexpr_parser.parse(special_var + " >= " + number) 
                            self.cond_vars.add(special_var)
                else:
                    # self.condition =bexpr_parser.parse(str(func.cond))
                    self.condition =func.cond
            else:
                self.condition =None
            if isinstance(func.cond_act,hp.Sequence):
                # for cond_act in func.cond_act.hps:
                #     if isinstance(cond_act,Assign):
                #         if isinstance(cond_act.var_name,ListExpr):
                #             for arg in cond_act.var_name.args:
                #                 print(arg)
                #                 print(type(arg))
                self.cond_acts=[cond_act for cond_act in func.cond_act.hps] 
                # self.cond_acts=[str(cond_act) for cond_act in func.cond_act.hps] 
            elif func.cond_act:
                self.cond_acts = [func.cond_act]
                # self.cond_acts = [str(func.cond_act)]
            else:
                self.cond_act =[]
            if isinstance(func.tran_act,hp.Sequence):
                self.tran_acts=[tran_act for tran_act in func.tran_act.hps]  
                # self.tran_acts=[str(tran_act) for tran_act in func.tran_act.hps]  
            elif func.tran_act:
                self.tran_acts = [func.tran_act]
                # self.tran_acts = [str(func.tran_act)]
            else:
                self.tran_acts=[]
            if func.event:
                if isinstance(func.event,FunExpr):
                    if func.event.fun_name == "after":
                        # Parse after(number, event) condition
                        # number, event = condition[6:-1].split(",")
                        number, event = str(func.event.exprs[0]),str(func.event.exprs[1])
                        if event == "sec":
                            special_var = "state_time"+str(self.src)
                            if self.condition is not None:
                                self.condition =bexpr_parser.parse(str(self.condition)+"&&"+special_var + " >= " + number)    #？？？？？？
                            else:
                                self.condition =bexpr_parser.parse(special_var + " >= " + number) 
                            self.cond_vars.add(special_var)
                          
                else:
                    self.event =str(func.event)
            else:
                self.event = None
        
        # label = self.label if self.label else ""
        # # Get transition condition
        # cond_pattern = "\\[.*?\\]"
        # conditions = re.findall(pattern=cond_pattern, string=label)
        # # if len(conditions2)>0:
        # for c in conditions:
           
        #     if re.match(pattern="\\[(\\w+(,)?)*(\\w+\\(\\w*(,\\w*)*\\))*((,)?\\w+)*((,)?\\w+\\(\\w*(,\\w*)*\\))*\\]", string=c):
        #     # if re.match(pattern="\\[.*?,.*?\\]", string=c):
        #         conditions.remove(c)
        # # conditions=""
        
        # # if len(conditions1) >1:
        # #     conditions=[conditions1[0]]
        # # else:
        # #     conditions=conditions1
        # assert len(conditions) <= 1
        # if conditions:
        #     condition = conditions[0].strip("[]")    #删除开头和结尾的[]
        #     if re.match(pattern="after\\(.*?,.*?\\)", string=condition):
        #         # Parse after(number, event) condition
        #         # number, event = condition[6:-1].split(",")
        #         number, event = [e.strip() for e in condition[6:-1].split(",")]
        #         if event == "sec":
        #             special_var = "state_time"
        #             self.condition = bexpr_parser.parse(special_var + " >= " + number)    #？？？？？？
        #             self.cond_vars.add(special_var)
        #     elif re.match(pattern="before\\(.*?,.*?\\)", string=condition):
        #         # Parse after(number, event) condition
        #         # number, event = condition[6:-1].split(",")
        #         number, event = [e.strip() for e in condition[7:-1].split(",")]
        #         if event == "sec":
        #             special_var = "state_time"
        #             self.condition = bexpr_parser.parse(special_var + " < " + number)    #？？？？？？
        #             self.cond_vars.add(special_var)
        #     elif re.match(pattern="at\\(.*?,.*?\\)", string=condition):
        #         # Parse after(number, event) condition
        #         # number, event = condition[6:-1].split(",")
        #         number, event = [e.strip() for e in condition[7:-1].split(",")]
        #         if event == "tick":
        #             special_var = "state_time"
        #             self.condition = bexpr_parser.parse(special_var + " == " + number) 
        #             self.cond_vars.add(special_var)
        #     elif "." in condition and "==" in condition:
        #         left,right=condition.split("==")
        #         left1,left2=left.split(".")
        #         self.condition=bexpr_parser.parse(left1+"_"+left2+" == "+right)
        #     else:
        #         self.condition = bexpr_parser.parse(condition)
        # else:
        #     self.condition = None
        # # self.condition = bexpr_parser.parse(conditions[0].strip("[]")) if conditions else None
        # # Delete transition condition
        # if len(conditions)>0:
        #     label = label.replace(conditions[0],"")
        # # Get transition action
        # tran_act_pattern = "/{.*?}"
        # tran_acts = re.findall(pattern=tran_act_pattern, string=label)
        # assert len(tran_acts) <= 1
        # # tran_act = None
        # if tran_acts:
        #     self.tran_acts = [act.strip() for act in
        #                       re.sub(pattern="=", repl=":=", string=tran_acts[0].strip("/{;}")).split(";")]
        # # Delete transition action
        # label = re.sub(pattern=tran_act_pattern, repl="", string=label)

        # # Get condition action
        # cond_act_pattern = "{.*?}"
        # cond_acts = re.findall(pattern=cond_act_pattern, string=label)
        # assert len(cond_acts) <= 1
        # # cond_act = None
        # if cond_acts:
        #     self.cond_acts = [act.strip() for act in
        #                       re.sub(pattern="=", repl=":=", string=cond_acts[0].strip("{;}")).split(";")]
        # # Delete condition action
        # label = re.sub(pattern=cond_act_pattern, repl="", string=label)
        # #没处理完条件或条件操作或转换操作将其置为空
        # # Get event
        # #assert all(symbol not in label for symbol in "[]{}/;")
        # if re.match(pattern="after\\(.*?,.*?\\)", string=label):
        #         # Parse after(number, event) condition
        #         # number, event = condition[6:-1].split(",")
        #         number, event = [e.strip() for e in label[6:-1].split(",")]
        #         if event == "sec":
        #             special_var = "state_time"
        #             if self.condition is not None:
        #                 self.condition =bexpr_parser.parse(str(self.condition)+"&&"+special_var + " >= " + number)    #？？？？？？
        #             else:
        #                 self.condition =bexpr_parser.parse(special_var + " >= " + number) 
        #             self.cond_vars.add(special_var)
        #             label = re.sub(pattern="after\\(.*?,.*?\\)", repl="", string=label)

        #         # elif event == "tick":
        #         #     special_var = "state_time"
        #         #     self.condition = bexpr_parser.parse(special_var + " >= " + number)    #？？？？？？
        #         #     self.cond_vars.add(special_var)
        # elif re.match(pattern="before\\(.*?,.*?\\)", string=label):
        #         # Parse after(number, event) condition
        #         # number, event = condition[6:-1].split(",")
        #         number, event = [e.strip() for e in label[7:-1].split(",")]
        #         if event == "sec":
        #             special_var = "state_time"
        #             self.condition = bexpr_parser.parse(special_var + " < " + number)    #？？？？？？
        #             self.cond_vars.add(special_var)
        #             label = re.sub(pattern="before\\(.*?,.*?\\)", repl="", string=label)
        # else:
        #     if label == "":
        #         self.event=None
        #     else:
        #         self.event=label
        # Assertion on default transitions
        # if self.src is None:  # a default transition
        #     assert self.condition is None and self.event == ""
    def get_vars(self):
        var_set = set()       #无序不重复
        # Get variables in condition
        if self.condition:
            assert isinstance(self.condition, BExpr)
            var_set = var_set.union(self.condition.get_vars())    #返回两个集合的交集
        # Get variables in actions
        for act in list(self.cond_acts) + list(self.tran_acts):
            assert isinstance(act, (hp.HCSP,str))
            if isinstance(act, (hp.Assign, hp.Sequence)) :
                var_set = var_set.union(act.get_vars())
        return var_set
