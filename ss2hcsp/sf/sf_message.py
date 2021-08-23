"""Data and messages in Stateflow."""

from ss2hcsp.matlab import function


class SF_Message:
    """docstring for SF_Message"""
    def __init__(self, name="",data="",scope=None):
        self.name = name
        self.data = data
        self.scope = scope

    def __str__(self):
            return "{ 'name':'%s' , 'data':%s , 'scope':'%s'}" % (self.name, self.data,self.scope)

    def __repr__(self):
        return "Message(%s,%s,%s)" % (self.name, self.data, self.scope)

    def keys(self):
        return ('name', 'data', 'scope')

    def __getitem__(self, item):
        return getattr(self, item)


class SF_Data:
    """Represents Stateflow data object."""
    def __init__(self, name, value, scope):
        super(SF_Data, self).__init__()
        assert isinstance(name, str) and isinstance(scope, str)
        if value is not None:
            assert isinstance(value, (function.Expr,int))
        self.name = name
        self.value = value
        self.scope = scope

    def __str__(self):
        return "SF_Data(%s = %s; scope:%s)" % (self.name, self.value, self.scope)
        
    def __repr__(self):
        return "SF_Data(%s,%s,%s)" % (repr(self.name), repr(self.value), repr(self.scope))
