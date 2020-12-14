"""Modules for hybrid programs"""

class HCSPModule:
    """An HCSP module can be considered as a template for HCSP processes.
    It contains a list of parameters that can be substituted for channel
    names and variables in the module.
    
    """
    def __init__(self, name, params, outputs, code):
        self.name = name
        self.params = params
        self.outputs = outputs
        self.code = code

    def __str__(self):
        return self.name + '(' + ','.join(self.params) + ')'

    def __repr__(self):
        if self.params:
            return "Module(%s,%s)" % (self.name, ','.join(self.params))
        else:
            return "Module(%s)" % self.name


class HCSPSystem:
    """An HCSP system keeps a list of modules and their instantiations.
    
    This class keeps sufficient information to reconstruct the parallel
    HCSP process.
    
    """
    def __init__(self, args):
        self.args = args

    def __str__(self):
        def print_arg(arg):
            return "%s(%s)" % (arg[0], ','.join(arg[1:]))
        return ' || '.join(print_arg(arg) for arg in self.args)

    def __repr__(self):
        def print_arg(arg):
            return "%s(%s)" % (arg[0], ','.join(arg[1:]))
        return "System(%s)" % ("; ".join(print_arg(arg) for arg in self.args))


class HCSPDeclarations:
    """A list of HCSP declarations.
    
    Contains a number of module declarations (HCSPModule) and a single
    system declaration (HCSPSystem).

    """
    def __init__(self, args):
        self.args = args

    def __str__(self):
        return '\n'.join(str(arg) for arg in self.args)

    def __repr__(self):
        return "Decls(\n  %s\n)" % ('\n  '.join(repr(arg) for arg in self.args))
