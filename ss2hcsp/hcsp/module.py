"""Modules for hybrid programs"""

import os

from ss2hcsp.hcsp.hcsp import HCSPInfo, Channel


class ModuleException(Exception):
    def __init__(self, error_msg):
        self.error_msg = error_msg


class HCSPModule:
    """An HCSP module can be considered as a template for HCSP processes.
    It contains a list of parameters that can be substituted for channel
    names and variables in the module.
    
    """
    def __init__(self, name, params, outputs, code):
        self.name = name
        self.params = params
        self.outputs = outputs
        if isinstance(code, str):
            code = hp_parser.parse(code)
        self.code = code

    def __str__(self):
        return self.name + '(' + ','.join(self.params) + ')'

    def __repr__(self):
        if self.params:
            return "Module(%s,%s)" % (self.name, ','.join(self.params))
        else:
            return "Module(%s)" % self.name


class HCSPModuleInst:
    """An instantiation of an HCSP module.

    Maintains name of the resulting process, name of the HCSP module
    to be instantiated, and list of concrete argments for the parameters.

    """
    def __init__(self, name, module_name, args):
        self.name = name
        self.module_name = module_name
        self.args = args

    def __str__(self):
        if self.name == self.module_name:
            return "%s(%s)" % (self.module_name, ','.join(str(arg) for arg in self.args))
        else:
            return "%s=%s(%s)" % (self.name, self.module_name,
                ','.join(str(arg) for arg in self.args))

    def __repr__(self):
        if self.args:
            return "ModuleInst(%s,%s)" % (self.name, self.module_name)
        else:
            return "ModuleInst(%s,%s,%s)" % (self.name, self.module_name,
                ','.join(str(arg) for arg in self.args))

    def generateInst(self, module):
        """Given the module, construct the corresponding HCSP info."""

        # First, construct the mapping between formal and actual parameters
        inst = dict()
        if len(module.params) != len(self.args):
            raise ModuleException("Number of arguments for %s does not match: %s vs %s" % (
                self.name, len(module.params), len(self.args)))
        for param, arg in zip(module.params, self.args):
            inst[param] = arg
        
        return HCSPInfo(self.name, module.code.subst_comm(inst), outputs=module.outputs)


class HCSPSystem:
    """An HCSP system keeps a list of module instantiations.
    
    This class keeps sufficient information to reconstruct the parallel
    HCSP process.
    
    """
    def __init__(self, module_insts):
        self.module_insts = module_insts

    def __str__(self):
        return ' || '.join(str(module_inst) for module_inst in self.module_insts)

    def __repr__(self):
        return "System(%s)" % ("; ".join(str(module_inst) for module_inst in self.module_insts))


hcsp_import_path = [
    './ss2hcsp/common',
]

# Read additional import path from import_path.txt
try:
    hcsp_import_path = [os.path.abspath(path) for path in hcsp_import_path]
    with open('./ss2hcsp/import_path.txt') as f:
        for line in f.readlines():
            hcsp_import_path.append(os.path.abspath(line.strip()))
except FileNotFoundError:
    print('Warning: import_path.txt not found.')

def read_file(filename):
    """Given file name, attempt to locate the file in the import paths
    in reverse order. Returns the content of the file. If the file is not
    found, return None.

    """
    for path in reversed(hcsp_import_path):
        try:
            print('Opening:', os.path.join(path, filename))
            with open(os.path.join(path, filename), encoding='utf-8') as f:
                text = f.read()
            return text
        except FileNotFoundError:
            pass
    
    return None


class HCSPDeclarations:
    """A list of HCSP declarations.
    
    Contains a number of module declarations (HCSPModule) and a single
    system declaration (HCSPSystem).

    """
    def __init__(self, args):
        """Input is a list of HCSPModule, HCSPSystem, or
        HCSPDeclaration objects. The HCSPDeclaration objects are unfolded.
        
        Should contain exactly one HCSPSystem.

        """
        # Mapping from module name to HCSPModule
        self.modules = dict()

        # Overall system
        self.system = None

        for arg in args:
            if isinstance(arg, HCSPModule):
                if arg.name in self.modules:
                    raise ModuleException("Module name %s is repeated" % arg.name)
                self.modules[arg.name] = arg

            elif isinstance(arg, HCSPSystem):
                if self.system is not None:
                    raise ModuleException("More than one system in declaration")
                self.system = arg

            elif isinstance(arg, HCSPDeclarations):
                for name in arg.modules:
                    if name in self.modules:
                        raise ModuleException("Import name %s is repeated" % name)
                    self.modules[name] = arg.modules[name]

            else:
                raise NotImplementedError

    def __str__(self):
        res = ""
        for name in sorted(self.modules.keys()):
            res += str(self.modules[name]) + '\n'
        res += str(self.system)
        return res

    def __repr__(self):
        res = "Decls(\n"
        for name in sorted(self.modules.keys()):
            res += '  ' + repr(self.modules[name]) + '\n'
        res += '  ' + repr(self.system) + '\n)'
        return res

    def generateHCSPInfo(self):
        """Produce list of HCSPInfo objects."""
        if self.system is None:
            raise ModuleException("No system in declaration")

        infos = []
        for module_inst in self.system.module_insts:
            if module_inst.module_name not in self.modules:
                raise ModuleException(
                    "generateHCSPInfo: %s not found in declaration" % module_inst.module_name)

            module = self.modules[module_inst.module_name]
            hcsp_info = module_inst.generateInst(module)
            infos.append(hcsp_info)

        return infos
