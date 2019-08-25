import re


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
        label = self.label

        # Get transition condition
        cond_pattern = "\\[.*?\\]"
        conditions = re.findall(pattern=cond_pattern, string=label)
        assert len(conditions) <= 1
        condition = conditions[0].strip("[]") if conditions else ""
        # Delete transition condition
        label = re.sub(pattern=cond_pattern, repl="", string=label)

        # Get transition action
        tran_act_pattern = "/{.*?}"
        tran_acts = re.findall(pattern=tran_act_pattern, string=label)
        assert len(tran_acts) <= 1
        tran_act = tran_acts[0].strip("/{;}") if tran_acts else ""
        # Delete transition action
        label = re.sub(pattern=tran_act_pattern, repl="", string=label)

        # Get condition action
        cond_act_pattern = "{.*?}"
        cond_acts = re.findall(pattern=cond_act_pattern, string=label)
        assert len(cond_acts) <= 1
        cond_act = cond_acts[0].strip("{;}") if cond_acts else ""
        # Delete condition action
        label = re.sub(pattern=cond_act_pattern, repl="", string=label)

        # Get event
        for symbol in "[]{}/;":
            assert symbol not in label
        event = label

        return event, condition, cond_act, tran_act
