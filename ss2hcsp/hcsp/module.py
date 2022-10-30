"""Modules for hybrid programs"""

import os
from typing import List, Optional, Tuple, Union

from ss2hcsp.hcsp.hcsp import HCSPInfo, Procedure, HCSP
from ss2hcsp.hcsp import pprint
from ss2hcsp.hcsp import expr


class ModuleException(Exception):
    def __init__(self, error_msg):
        self.error_msg = error_msg


class HCSPModule:
    """Template for an HCSP process.

    name: name of the module.
    params: list of parameters that can be substituted for channel names
        and variables in the module.
    outputs: list of output variables.
    procedures: list of declared procedures.
    code: code (template) for the main process.
    
    """
    def __init__(self, name: str, code: Union[str, HCSP], *, params=None,
                 outputs=None, procedures=None, meta=None):
        self.name = name
        if params is None:
            params = tuple()
        self.params = tuple(params)
        if outputs is None:
            outputs = tuple()
        self.outputs = tuple(outputs)
        if procedures is None:
            procedures = []
        self.procedures = procedures
        if isinstance(code, str):
            from ss2hcsp.hcsp.parser import hp_parser
            code = hp_parser.parse(code)
        self.code = code
        self.meta = meta

    def __eq__(self, other):
        return self.name == other.name and self.params == other.params and \
            self.outputs == other.outputs and self.procedures == other.procedures and \
            self.code == other.code

    def __str__(self):
        return self.name + '(' + ','.join(self.params) + ')'

    def __repr__(self):
        if self.params:
            return "Module(%s,%s)" % (self.name, ','.join(self.params))
        else:
            return "Module(%s)" % self.name

    def export(self):
        """Print the string that will parse to the module."""
        def str_of_outputs(outputs):
            if outputs:
                return "output %s;\n" % (', '.join(str(output) for output in outputs))
            else:
                return ""

        def str_of_procedure(procedures):
            res = ""
            for procedure in procedures:
                res += "procedure %s begin\n" % procedure.name
                body = pprint.pprint(procedure.hp)
                for line in body.split('\n'):
                    res += "  " + line + "\n"
                res += "end\n\n"
            return res

        def str_of_code(code):
            res = ""
            code_str = pprint.pprint(code)
            for line in code_str.split('\n'):
                res += "  " + line + "\n"
            return res

        res = "module %s(%s):\n%s%sbegin\n%send\nendmodule" % (
            self.name,
            ','.join(self.params),
            str_of_outputs(self.outputs),
            str_of_procedure(self.procedures),
            str_of_code(self.code)
        )
        return res


class HCSPModuleInst:
    """An instantiation of an HCSP module.

    Maintains name of the resulting process, name of the HCSP module
    to be instantiated, and list of concrete argments for the parameters.

    """
    def __init__(self, name: str, module_name: str, args: Optional[Tuple[expr.Expr]]=None, meta=None):
        self.name: str = name
        self.module_name: str = module_name
        self.args: Tuple[expr.Expr] = tuple()
        if args is not None:
            self.args = tuple(args)
        self.meta = meta

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

    def export(self) -> str:
        """Print the string that will parse to the module instantiation."""
        def print_arg(arg):
            if isinstance(arg, expr.AConst):
                if isinstance(arg.value, str) and arg.value[0] != "\"":
                    return "$\"" + arg.value + "\""
                else:
                    return "$" + str(arg.value)
            else:
                return str(arg)
        
        
        if self.name == self.module_name:
            return "%s(%s)" % (self.name,
                ', '.join(print_arg(arg) for arg in self.args))
        else:
            return "%s = %s(%s)" % (self.name, self.module_name,
                ', '.join(print_arg(arg) for arg in self.args))

    def generateInst(self, module: HCSPModule) -> HCSPInfo:
        """Given the module, construct the corresponding HCSP info."""

        # First, construct the mapping between formal and actual parameters
        inst = dict()
        if len(module.params) != len(self.args):
            raise ModuleException("Number of arguments for %s does not match: %s vs %s" % (
                self.name, len(module.params), len(self.args)))
        for param, arg in zip(module.params, self.args):
            inst[param] = arg

        # Next, instantiate code and each procedure
        code = module.code.subst_comm(inst)
        procedures = [Procedure(proc.name, proc.hp.subst_comm(inst)) for proc in module.procedures]
        
        return HCSPInfo(self.name, code, outputs=module.outputs, procedures=procedures)


class HCSPSystem:
    """An HCSP system keeps a list of module instantiations.
    
    This class keeps sufficient information to reconstruct the parallel
    HCSP process.
    
    """
    def __init__(self, module_insts: List[HCSPModuleInst], meta=None):
        self.module_insts = module_insts
        self.meta = meta

    def __str__(self):
        return ' ||\n'.join(module_inst.export() for module_inst in self.module_insts)

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
    pass
    # print('Warning: import_path.txt not found.')

def read_file(filename):
    """Given file name, attempt to locate the file in the import paths
    in reverse order. Returns the content of the file. If the file is not
    found, return None.

    """
    for path in reversed(hcsp_import_path):
        try:
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
    def __init__(self, args, meta=None):
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
                print(arg, type(arg))
                raise NotImplementedError
        self.meta = meta

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

    def export(self) -> str:
        """Convert declarations to string that can be written to a file."""
        res = "%type: module\n\n"
        for name, m in self.modules.items():
            res += m.export() + "\n\n"
        res += "system\n" + str(self.system) + "\nendsystem\n"
        return res

    def generateHCSPInfo(self) -> List[HCSPInfo]:
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
