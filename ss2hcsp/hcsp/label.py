"""Label System for distinguishing verification conditions"""
class Label:
    def __init__(self):
        pass


class BranchLabel(Label):
    """Label that records the executed program branches, 
    which generate the corresponding verification conditions.
    """
    def __init__(self):
        pass


class AtomLabel(BranchLabel):
    """Label that records which program branch executed in ITE, IChoice or ODE.
    Example: 1 or skip"""
    def __init__(self, value):
        assert isinstance(value, (str, int))
        self.value = value

    def __str__(self):
        return str(self.value)


class SequenceLabel(BranchLabel):
    """Label that records the program branch executed in a Sequence program.
    Example: 1.2.1"""
    def __init__(self, *labels):
        assert all(isinstance(lb, BranchLabel) for lb in labels)
        self.labels = tuple(labels)

    def __str__(self):
        return ".".join(str(lb) for lb in self.labels)


class NestLabel(BranchLabel):
    """Label that records the program branch executed in a nested program
    Example 1(2)"""
    def __init__(self, value, sub_label):
        assert isinstance(value, (int, str))
        assert isinstance(sub_label, BranchLabel)
        self.value = value
        self.sub_label = sub_label

    def __str__(self):
        return str(self.value) + "(" + str(self.sub_label) + ")"

# class BranchLabel(Label):
#     """Label that records the executed program branches, 
#     which generate the corresponding verification conditions.
    
#     BranchLabel is a tree structure:
#         value: the executed branch index of the current program
#         child_labels: the executed branch labels of the child-programs
        
#     Examples:
#         1: value is 1, child_label is ()
#         1.1.2: value is None, child_labels is (BranchLabel(1), BranchLabel(1), BranchLabel(2))
#         1(2): value is 1, chilf_labels is (BranchLabel(2))"""
#     def __init__(self, value=None, *child_labels):
#         if value:
#             assert isinstance(value, (str, int))
#         assert all(isinstance(child_label, BranchLabel) for child_label in child_labels)
#         self.value = value
#         self.child_labels = tuple(child_labels)

#     def __str__(self):
#         if self.value and self.child_labels:
#             return str(self.value) + "(" + ".".join(str(child_label) for child_label in self.child_labels) + ")"

#         elif not self.value and self.child_labels:
#             return ".".join(str(child_label) for child_label in self.child_labels)

#         elif self.value and not self.child_labels:
#             return str(self.value)
        
#         else:
#             raise NotImplementedError


class CompLabel(Label):
    """Label that is composed of category and branch_label
    Example: init1.1"""
    def __init__(self, categ, branch_label):
        assert isinstance(categ, str)
        self.categ = categ
        assert isinstance(branch_label, BranchLabel)
        self.branch_label = branch_label

    def __str__(self):
        return self.categ + str(self.branch_label)