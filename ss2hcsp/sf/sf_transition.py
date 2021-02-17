import re
from ss2hcsp.hcsp.parser import bexpr_parser
from ss2hcsp.hcsp.expr import BExpr
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.hcsp import OutputChannel


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
        label = self.label if self.label else ""
        # Get transition condition
        cond_pattern = "\\[.*?\\]"
        conditions = re.findall(pattern=cond_pattern, string=label)
        assert len(conditions) <= 1
        if conditions:
            condition = conditions[0].strip("[]")    #删除开头和结尾的[]
            if re.match(pattern="after\\(.*?,.*?\\)", string=condition):
                # Parse after(number, event) condition
                # number, event = condition[6:-1].split(",")
                number, event = [e.strip() for e in condition[6:-1].split(",")]
                if event == "sec":
                    special_var = "state_time"
                    self.condition = bexpr_parser.parse(special_var + " >= " + number)    #？？？？？？
                    self.cond_vars.add(special_var)
            elif "." in condition and "==" in condition:
                left,right=condition.split("==")
                left1,left2=left.split(".")
                self.condition=bexpr_parser.parse(left1+"_"+left2+" == "+right)
            else:
                self.condition = bexpr_parser.parse(condition)
        else:
            self.condition = None
        # self.condition = bexpr_parser.parse(conditions[0].strip("[]")) if conditions else None
        # Delete transition condition
        label = re.sub(pattern=cond_pattern, repl="", string=label)

        # Get transition action
        tran_act_pattern = "/{.*?}"
        tran_acts = re.findall(pattern=tran_act_pattern, string=label)
        assert len(tran_acts) <= 1
        # tran_act = None
        if tran_acts:
            self.tran_acts = [act.strip() for act in
                              re.sub(pattern="=", repl=":=", string=tran_acts[0].strip("/{;}")).split(";")]
        # Delete transition action
        label = re.sub(pattern=tran_act_pattern, repl="", string=label)

        # Get condition action
        cond_act_pattern = "{.*?}"
        cond_acts = re.findall(pattern=cond_act_pattern, string=label)
        assert len(cond_acts) <= 1
        # cond_act = None
        if cond_acts:
            self.cond_acts = [act.strip() for act in
                              re.sub(pattern="=", repl=":=", string=cond_acts[0].strip("{;}")).split(";")]
        # Delete condition action
        label = re.sub(pattern=cond_act_pattern, repl="", string=label)
        #没处理完条件或条件操作或转换操作将其置为空
        # Get event
        #assert all(symbol not in label for symbol in "[]{}/;")
        self.event = label
        # Assertion on default transitions
        if self.src is None:  # a default transition
            assert self.condition is None and self.event == ""

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
