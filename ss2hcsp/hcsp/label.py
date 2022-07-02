"""Label System for distinguishing verification conditions"""
class Label:
    def __init__(self):
        pass


class BranchLabel(Label):
    """Label that records the executed program branches, 
    which generate the corresponding verification conditions.
    
    BranchLabel is a tree structure:
        value: the executed branch index of the current program
        child_labels: the executed branch labels of the child-programs
        
    Examples:
        1: value is 1, child_label is ()
        1.1.2: value is None, child_labels is (BranchLabel(1), BranchLabel(1), BranchLabel(2))
        1(2): value is 1, chilf_labels is (BranchLabel(2))"""
    def __init__(self, value=None, *child_labels):
        if value:
            assert isinstance(value, (str, int))
        assert all(isinstance(child_label, BranchLabel) for child_label in child_labels)
        self.value = value
        self.child_labels = tuple(child_labels)

    def __str__(self):
        if self.value and self.child_labels:
            return str(self.value) + "(" + ".".join(str(child_label) for child_label in self.child_labels) + ")"

        elif not self.value and self.child_labels:
            return ".".join(str(child_label) for child_label in self.child_labels)

        elif self.value and not self.child_labels:
            return str(self.value)
        
        else:
            raise NotImplementedError


class CompLabel(Label):
    """Label that is composed of category and branch_label
    Example: init1.1"""
    def __init__(self, categ=None, branch_label=None):
        if categ:
            assert isinstance(categ, str)
            self.categ = categ
        if branch_label:
            assert isinstance(branch_label, BranchLabel)
            self.branch_label = branch_label