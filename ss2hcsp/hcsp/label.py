"""Label System for distinguishing verification conditions"""
class Label:
    def __init__(self):
        pass


class BranchLabel(Label):
    """Label that records the executed program branches, 
    which generate the corresponding verification conditions.
    """
    def __init__(self):
        super(BranchLabel, self).__init__()
        pass


class AtomLabel(BranchLabel):
    """Label that records which program branch executed in ITE, IChoice or ODE.
    Example: 1 or skip"""
    def __init__(self, value):
        super(AtomLabel, self).__init__()
        assert isinstance(value, (str, int))
        self.value = value

    def __str__(self):
        return str(self.value)


class SequenceLabel(BranchLabel):
    """Label that records the program branch executed in a Sequence program.
    Example: 1.2.1"""
    def __init__(self, *labels):
        super(SequenceLabel, self).__init__()
        assert all(isinstance(lb, BranchLabel) or lb is None for lb in labels) # arguments can be None
        valid_labels = [lb for lb in labels if lb]
        assert len(valid_labels)
        self.labels = tuple(valid_labels)  # Only consider the valid labels

    def __str__(self):
        return ".".join(str(lb) for lb in self.labels)


class NestLabel(BranchLabel):
    """Label that records the program branch executed in a nested program
    Example 1(2)"""
    def __init__(self, value, sub_label):
        super(NestLabel, self).__init__()
        assert isinstance(value, (int, str))
        assert isinstance(sub_label, BranchLabel)
        self.value = value
        self.sub_label = sub_label

    def __str__(self):
        return str(self.value) + "(" + str(self.sub_label) + ")"


class CategLabel(Label):
    """Label that records the category.
    Example: init"""
    def __init__(self, categ):
        super(CategLabel, self).__init__()
        assert isinstance(categ, str)
        self.categ = categ

    def __str__(self):
        return str(self.categ)


class CompLabel(Label):
    """Label that is composed of category and branch_label.
    Example: init 1.1"""
    def __init__(self, categ_label, branch_label):
        super(CompLabel, self).__init__()
        assert isinstance(categ_label, CategLabel)
        assert isinstance(branch_label, BranchLabel)
        self.categ_label = categ_label
        self.branch_label = branch_label

    def __str__(self):
        return str(self.categ_label) + ' ' + str(self.branch_label)