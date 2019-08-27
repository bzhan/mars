import re
from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser
# from ss2hcsp.hcsp import hcsp as hp


class Transition:
    def __init__(self, ssid, label, order=0, src="", dst=""):
        self.ssid = ssid
        self.label = label
        self.order = order
        self.src = src
        self.dst = dst

    def __str__(self):
        return "Tran(%s)--%s-->" % (self.ssid, self.label)

    def __repr__(self):
        return "Transition(%s, %s, %s, %s, %s)" % \
               (self.ssid, self.label, self.order, self.src, self.dst)

    def parse(self):
        label = self.label if self.label else ""

        # Get transition condition
        cond_pattern = "\\[.*?\\]"
        conditions = re.findall(pattern=cond_pattern, string=label)
        assert len(conditions) <= 1
        condition = bexpr_parser.parse(conditions[0].strip("[]")) if conditions else None
        # Delete transition condition
        label = re.sub(pattern=cond_pattern, repl="", string=label)

        # Get transition action
        tran_act_pattern = "/{.*?}"
        tran_acts = re.findall(pattern=tran_act_pattern, string=label)
        assert len(tran_acts) <= 1
        tran_act = None
        if tran_acts:
            tran_act = re.sub(pattern="=", repl=":=", string=tran_acts[0].strip("/{;}"))
            tran_act = hp_parser.parse(tran_act)
        # Delete transition action
        label = re.sub(pattern=tran_act_pattern, repl="", string=label)

        # Get condition action
        cond_act_pattern = "{.*?}"
        cond_acts = re.findall(pattern=cond_act_pattern, string=label)
        assert len(cond_acts) <= 1
        cond_act = None
        if cond_acts:
            cond_act = re.sub(pattern="=", repl=":=", string=cond_acts[0].strip("{;}"))
            cond_act = hp_parser.parse(cond_act)
        # Delete condition action
        label = re.sub(pattern=cond_act_pattern, repl="", string=label)

        # Get event
        for symbol in "[]{}/;":
            assert symbol not in label
        event = label

        # Assertion on default transitions
        if self.src is None:  # a default transition
            assert condition is None and tran_act is None and event == ""

        return event, condition, cond_act, tran_act
