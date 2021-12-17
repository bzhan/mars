"""Parser for expressions."""

from lark import Lark, Transformer, v_args, exceptions
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import module


grammar = r"""
    ?lname: CNAME -> var_expr
        | CNAME "[" expr "]" -> array_idx_expr
        | CNAME "[" expr "]" "[" expr "]" -> array_idx_expr2
        | CNAME "[" expr "]" "[" expr "]""[" expr "]" -> array_idx_expr3
        | lname "." CNAME -> field_expr
        | lname "." CNAME "[" expr "]" -> field_array_idx

    ?atom_expr: lname
        | SIGNED_NUMBER -> num_expr
        | ESCAPED_STRING -> string_expr
        | "[" "]" -> empty_list
        | "[" expr ("," expr)* "]" -> literal_list
        | "{" "}" -> empty_dict
        | "{" CNAME ":" expr ("," CNAME ":" expr)* "}" -> literal_dict
        | "min" "(" expr "," expr ")" -> min_expr
        | "max" "(" expr "," expr ")" -> max_expr
        | "gcd" "(" expr ("," expr)+ ")" -> gcd_expr
        | CNAME "(" (expr)? ("," expr)* ")" -> fun_expr
        | "(" expr ")"

    ?power_expr: power_expr "^" atom_expr -> power_expr    // priority 85
        | atom_expr

    ?uminus: "-" uminus -> uminus | power_expr              // Unary minus: priority 80

    ?times_expr: times_expr "*" uminus -> times_expr       // priority 70
        | times_expr "/" uminus -> divide_expr
        | times_expr "%" uminus -> mod_expr
        | uminus

    ?plus_expr: plus_expr "+" times_expr -> plus_expr      // priority 65
        | plus_expr "-" times_expr -> minus_expr
        | times_expr

    ?if_expr: "(" cond "?" if_expr ":" if_expr ")"         // priority 40
        | plus_expr

    ?expr: if_expr

    ?atom_cond: expr "==" expr -> eq_cond                  // priority 50
        | expr "!=" expr -> ineq_cond
        | expr "<=" expr -> less_eq_cond
        | expr "<" expr -> less_cond
        | expr ">=" expr -> greater_eq_cond
        | expr ">" expr -> greater_cond
        | "~" cond -> not_cond
        | "true" -> true_cond
        | "false" -> false_cond
        | "(" cond ")"
    
    ?conj: atom_cond "&&" conj | atom_cond       // Conjunction: priority 35

    ?disj: conj "||" disj | conj                 // Disjunction: priority 30

    ?imp: disj "-->" imp | disj                  // Implies: priority 25

    ?exists_expr: "EX" CNAME "." imp             // Exists: priority 10
        | imp

    ?cond: exists_expr

    ?comm_cmd: CNAME "?" lname -> input_cmd
        | CNAME "[" expr "]" "?" lname -> input_cmd
        | CNAME "[" expr "]" "[" expr "]" "?" lname -> input_cmd
        | CNAME "?" -> input_none_cmd
        | CNAME "[" expr "]" "?" -> input_none_cmd
        | CNAME "[" expr "]" "[" expr "]" "?" -> input_none_cmd
        | CNAME "!" expr -> output_cmd
        | CNAME "[" expr "]" "!" expr -> output_cmd
        | CNAME "[" expr "]" "[" expr "]" "!" expr -> output_cmd
        | CNAME "!" -> output_none_cmd
        | CNAME "[" expr "]" "!" -> output_none_cmd
        | CNAME "[" expr "]" "[" expr "]" "!" -> output_none_cmd

    ?ode_seq: CNAME "=" expr ("," CNAME "=" expr)*

    ?interrupt: comm_cmd "-->" cmd ("," comm_cmd "-->" cmd)*

    ?atom_cmd: "@" CNAME -> var_cmd
        | "skip" -> skip_cmd
        | "wait" "(" expr ")" -> wait_cmd
        | atom_expr ":=" expr -> assign_cmd
        | "(" lname ("," lname)* ")" ":=" expr -> multi_assign_cmd
        | atom_expr ":=" "{" cond "}" -> random_assign_cmd
        | "assert" "(" cond ("," expr)* ")" -> assert_cmd
        | "test" "(" cond ("," expr)* ")" -> test_cmd
        | "log" "(" expr ("," expr)* ")" -> log_cmd
        | comm_cmd
        | "(" cmd ")**" -> repeat_cmd
        | "(" cmd "){" cond "}**" -> repeat_cond_cmd
        | "(" cmd ")**@invariant(" cond ")" -> repeat_cmd_inv
        | "(" cmd "){" cond "}**@invariant(" cond ")" -> repeat_cond_cmd_inv
        | "<" ode_seq "&" cond ">" -> ode
        | "<" ode_seq "&" cond ">@invariant(" cond ")" -> ode_inv
        | "<" "&" cond ">" "|>" "[]" "(" interrupt ")" -> ode_comm_const
        | "<" ode_seq "&" cond ">" "|>" "[]" "(" interrupt ")" -> ode_comm
        | "rec" CNAME ".(" cmd ")" -> rec_cmd
        | "if" cond "then" cmd ("elif" cond "then" cmd)* "else" cmd "endif" -> ite_cmd 
        | "(" cmd ")" -> paren_cmd

    ?cond_cmd: atom_cmd | cond "->" atom_cmd       // Priority: 90

    ?ichoice_cmd: cond_cmd | ichoice_cmd "++" cond_cmd   // Priority: 80

    ?seq_cmd: ichoice_cmd (";" ichoice_cmd)*  // Priority: 70

    ?select_cmd: seq_cmd | comm_cmd "-->" seq_cmd ("$" comm_cmd "-->" seq_cmd)*  // Priority 50

    ?cmd: select_cmd

    ?procedure: "procedure" CNAME "begin" cmd "end"

    ?parallel_cmd: cmd ("||" cmd)*   // Priority 30, outermost level only

    ?module_sig: CNAME "(" (CNAME | "$" CNAME) ("," (CNAME | "$" CNAME))* ")"  -> module_sig
        | CNAME "(" ")"                            -> module_sig

    ?module_output: "output" CNAME ("," CNAME)* ";"    -> module_output
    
    ?module: "module" module_sig ":" (module_output)* (procedure)* "begin" cmd "end" "endmodule"
    
    ?module_arg: CNAME ("[" INT "]")*   -> module_arg_channel
        | "$" expr    -> module_arg_expr

    ?module_args: CNAME "(" module_arg ("," module_arg)* ")"  -> module_args
        | CNAME "(" ")"                            -> module_args

    ?module_inst: module_args    -> module_inst_noname
        | CNAME "=" module_args  -> module_inst

    ?system: "system" module_inst ("||" module_inst)* "endsystem"  -> system

    ?import: "import" CNAME   -> hcsp_import

    ?decls: "%type: module" (module | import | system)* -> decls

    %import common.CNAME
    %import common.WS
    %import common.INT
    %import common.DECIMAL
    %import common.NUMBER
    %import common.SIGNED_NUMBER
    %import common.ESCAPED_STRING

    %ignore WS
"""

@v_args(inline=True)
class HPTransformer(Transformer):
    def __init__(self):
        pass

    def var_expr(self, s):
        return expr.AVar(str(s))

    def num_expr(self, v):
        return expr.AConst(float(v) if '.' in v or 'e' in v else int(v))

    def string_expr(self, s):
        return expr.AConst(str(s)[1:-1])  # remove quotes

    def empty_list(self):
        return expr.ListExpr()

    def literal_list(self, *args):
        if all(isinstance(arg, expr.AConst) for arg in args):
            return expr.AConst(list(arg.value for arg in args))
        else:
            return expr.ListExpr(*args)

    def empty_dict(self):
        return expr.DictExpr()

    def literal_dict(self, *args):
        # args should contain 2*n elements, which are key-value pairs
        assert len(args) >= 2 and len(args) % 2 == 0
        pairs = []
        for i in range(0,len(args),2):
            pairs.append((str(args[i]), args[i+1]))
        return expr.DictExpr(*pairs)

    def array_idx_expr(self, a, i):
        return expr.ArrayIdxExpr(expr.AVar(str(a)), i)
    
    def array_idx_expr2(self, a, i, j):
        return expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.AVar(str(a)), i), j)

    def array_idx_expr3(self, a, i, j, k):
        return expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.AVar(str(a)), i), j), k)

    def field_array_idx(self, e, field, i):
        return expr.ArrayIdxExpr(expr.FieldNameExpr(e, field), i)

    def field_expr(self, e, field):
        return expr.FieldNameExpr(e, field)

    def if_expr(self, cond, e1, e2):
        return expr.IfExpr(cond, e1, e2)

    def exists_expr(self, var, e):
        return expr.ExistsExpr(str(var), e)

    def plus_expr(self, e1, e2):
        return expr.OpExpr("+", e1, e2)

    def minus_expr(self, e1, e2):
        return expr.OpExpr("-", e1, e2)

    def uminus(self, e):
        return expr.OpExpr("-", e)

    def times_expr(self, e1, e2):
        return expr.OpExpr("*", e1, e2)

    def divide_expr(self, e1, e2):
        return expr.OpExpr("/", e1, e2)

    def power_expr(self, e1, e2):
        return expr.OpExpr("^", e1, e2)

    def min_expr(self, e1, e2):
        return expr.FunExpr("min", [e1, e2])

    def max_expr(self, e1, e2):
        return expr.FunExpr("max", [e1, e2])

    def mod_expr(self, e1, e2):
        return expr.OpExpr("%", e1, e2)

    def gcd_expr(self, *exprs):
        return expr.FunExpr(fun_name="gcd", exprs=exprs)

    def fun_expr(self, fun_name, *exprs):
        return expr.FunExpr(fun_name, exprs)

    def eq_cond(self, e1, e2):
        return expr.RelExpr("==", e1, e2)

    def ineq_cond(self, e1, e2):
        return expr.RelExpr("!=", e1, e2)

    def less_eq_cond(self, e1, e2):
        return expr.RelExpr("<=", e1, e2)

    def less_cond(self, e1, e2):
        return expr.RelExpr("<", e1, e2)

    def greater_eq_cond(self, e1, e2):
        return expr.RelExpr(">=", e1, e2)

    def greater_cond(self, e1, e2):
        return expr.RelExpr(">", e1, e2)

    def not_cond(self, e):
        return expr.NegExpr(e)

    def true_cond(self):
        return expr.BConst(True)

    def false_cond(self):
        return expr.BConst(False)

    def conj(self, b1, b2):
        return expr.LogicExpr("&&", b1, b2)

    def disj(self, b1, b2):
        return expr.LogicExpr("||", b1, b2)

    def imp(self, b1, b2):
        return expr.LogicExpr("-->", b1, b2)

    def var_cmd(self, name):
        return hcsp.Var(str(name))

    def skip_cmd(self):
        return hcsp.Skip()

    def wait_cmd(self, delay):
        return hcsp.Wait(delay)

    def assign_cmd(self, var, expr):
        return hcsp.Assign(var, expr)

    def multi_assign_cmd(self, *args):
        return hcsp.Assign(args[:-1], args[-1])

    def random_assign_cmd(self, var, cond):
        return hcsp.RandomAssign(var, cond)

    def assert_cmd(self, *args):
        # First argument is the assert condition. The remaining ones
        # are error messages. 
        bexpr, msgs = args[0], args[1:]
        return hcsp.Assert(bexpr, msgs)

    def test_cmd(self, *args):
        # First argument is the test condition. The remaining ones
        # are warning messages.
        bexpr, msgs = args[0], args[1:]
        return hcsp.Test(bexpr, msgs)

    def log_cmd(self, *args):
        return hcsp.Log(args[0], exprs=args[1:])

    def seq_cmd(self, *args):
        if len(args) == 1:
            return args[0]
        else:
            return hcsp.Sequence(*args)

    def input_cmd(self, *args):
        # First argument is channel name, last argument is variable name.
        # Middle arguments are args to channel name.
        ch_name, ch_args, var_name = args[0], args[1:-1], args[-1]
        return hcsp.InputChannel(hcsp.Channel(str(ch_name), ch_args), var_name)

    def input_none_cmd(self, *args):
        # First argument is channel name, remaining arguments are its args.
        ch_name, ch_args = args[0], args[1:]
        return hcsp.InputChannel(hcsp.Channel(str(ch_name), ch_args))

    def output_cmd(self, *args):
        # First argument is channel name, last argument is variable name.
        # Middle arguments are args to channel name.
        ch_name, ch_args, expr = args[0], args[1:-1], args[-1]
        return hcsp.OutputChannel(hcsp.Channel(str(ch_name), ch_args), expr)

    def output_none_cmd(self, *args):
        # First argument is channel name, remaining arguments are its args.
        ch_name, ch_args = args[0], args[1:]
        return hcsp.OutputChannel(hcsp.Channel(str(ch_name), ch_args))

    def repeat_cmd(self, cmd):
        return hcsp.Loop(cmd)

    def repeat_cond_cmd(self, cmd, cond):
        return hcsp.Loop(cmd, constraint=cond)

    def repeat_cmd_inv(self, cmd, inv):
        return hcsp.Loop(cmd, inv=inv)

    def repeat_cond_cmd_inv(self, cmd, inv, cond):
        return hcsp.Loop(cmd, inv=inv, constraint=cond)

    def ode_seq(self, *args):
        res = []
        for i in range(0,len(args),2):
            assert args[i].endswith("_dot")
            res.append((str(args[i][:-4]), args[i+1]))
        return res

    def interrupt(self, *args):
        res = []
        for i in range(0, len(args), 2):
            res.append((args[i], args[i+1]))
        return res

    def ode(self, eqs, constraint):
        return hcsp.ODE(eqs, constraint)

    def ode_comm_const(self, constraint, io_comms):
        return hcsp.ODE_Comm([], constraint, io_comms)

    def ode_comm(self, eqs, constraint, io_comms):
        return hcsp.ODE_Comm(eqs, constraint, io_comms)

    def cond_cmd(self, cond, cmd):
        return hcsp.Condition(cond=cond, hp=cmd)

    def ichoice_cmd(self, cmd1, cmd2):
        return hcsp.IChoice(cmd1, cmd2)

    def select_cmd(self, *args):
        assert len(args) % 2 == 0 and len(args) >= 4
        io_comms = []
        for i in range(0, len(args), 2):
            io_comms.append((args[i], args[i+1]))
        return hcsp.SelectComm(*io_comms)

    def rec_cmd(self, var_name, c):
        return hcsp.Recursion(c, entry=var_name)

    def ite_cmd(self, *args):
        assert len(args) % 2 == 1 and len(args) >= 3
        if_hps = []
        for i in range(0, len(args)-1, 2):
            if_hps.append((args[i], args[i+1]))
        else_hp = args[-1]
        return hcsp.ITE(if_hps, else_hp)

    def paren_cmd(self, c):
        return c

    def procedure(self, name, hp):
        return hcsp.Procedure(name, hp)

    def parallel_cmd(self, *args):
        if len(args) == 1:
            return args[0]
        else:
            return hcsp.Parallel(*args)

    def module_sig(self, *args):
        return tuple(str(arg) for arg in args)

    def module_output(self, *args):
        return tuple(str(arg) for arg in args)

    def module(self, *args):
        # The first item is a tuple consisting of name and list of parameters
        # The middle items are the output sequences or procedure declarations
        # The last item is code for the module
        assert len(args) >= 2
        sig, decls, code = args[0], args[1:-1], args[-1]
        if isinstance(sig, tuple):
            name, params = sig[0], sig[1:]
        else:
            name, params = sig, tuple()
        outputs, procedures = [], []
        for decl in decls:
            if isinstance(decl, tuple):
                outputs.append(decl)
            elif isinstance(decl, hcsp.Procedure):
                procedures.append(decl)
            else:
                raise NotImplementedError
        return module.HCSPModule(name, code, params=params, outputs=outputs, procedures=procedures)

    def module_arg_channel(self, *args):
        # First argument is channel name, remaining arguments are channel args.
        ch_name, ch_args = args[0], args[1:]
        return hcsp.Channel(str(ch_name), tuple(expr.AConst(ch_arg) for ch_arg in ch_args))

    def module_arg_expr(self, expr):
        return expr

    def module_args(self, *args):
        return args

    def module_inst(self, name, sig):
        return module.HCSPModuleInst(name, sig[0], sig[1:])
    
    def module_inst_noname(self, sig):
        return module.HCSPModuleInst(sig[0], sig[0], sig[1:])

    def hcsp_import(self, filename):
        # Importing from a file
        text = module.read_file(filename + '.txt')
        if text is None:
            raise ParseFileException('File %s not found' % filename)
        try:
            # Preprocessing: just remove comments
            text_lines = text.strip().split('\n')
            text = ""

            for line in text_lines:
                comment_pos = line.find('#')
                if comment_pos != -1:
                    line = line[:comment_pos]
                if line.strip() != "":
                    text += line + '\n'

            return decls_parser.parse(text)
        except (exceptions.UnexpectedToken, exceptions.UnexpectedCharacters) as e:
            error_str = "Unable to parse\n"
            for i, line in enumerate(text.split('\n')):
                error_str += line + '\n'
                if i == e.line - 1:
                    error_str += " " * (e.column-1) + "^" + '\n'
            raise ParseFileException(error_str)

    def system(self, *args):
        # Each item is a module instantiation
        return module.HCSPSystem(args)

    def decls(self, *args):
        # A list of declarations.
        return module.HCSPDeclarations(args)


aexpr_parser = Lark(grammar, start="expr", parser="lalr", transformer=HPTransformer())
bexpr_parser = Lark(grammar, start="cond", parser="lalr", transformer=HPTransformer())
hp_parser = Lark(grammar, start="parallel_cmd", parser="lalr", transformer=HPTransformer())
module_parser = Lark(grammar, start="module", parser="lalr", transformer=HPTransformer())
system_parser = Lark(grammar, start="system", parser="lalr", transformer=HPTransformer())
decls_parser = Lark(grammar, start="decls", parser="lalr", transformer=HPTransformer())


class ParseFileException(Exception):
    def __init__(self, error_msg):
        self.error_msg = error_msg


def parse_file(text):
    """Parsing regular HCSP files.

    Input is the string of the file. Output is a list of pairs (name, hp).

    """
    text_lines = text.strip().split('\n')
    hcsp_info = []

    # First, read lines from file, each line containing ::= means the
    # start of a new program.
    lines = []
    for line in text_lines:
        comment_pos = line.find('#')
        if comment_pos != -1:
            line = line[:comment_pos]
        if line.find('::=') != -1:
            lines.append(line)
        else:
            if line != "":
                if len(lines) == 0:
                    raise ParseFileException('Unexpected line: ' + line)
                lines[-1] += line + '\n'

    infos = []

    # Now each entry in lines represent the definition of a program.
    for line in lines:
        index = line.index('::=')
        name = line[:index].strip()
        hp_text = line[index+3:].strip()

        try:
            hp = hp_parser.parse(hp_text)
        except (exceptions.UnexpectedToken, exceptions.UnexpectedCharacters) as e:
            error_str = "Unable to parse\n"
            for i, line in enumerate(hp_text.split('\n')):
                error_str += line + '\n'
                if i == e.line - 1:
                    error_str += " " * (e.column-1) + "^" + '\n'
            raise ParseFileException(error_str)

        infos.append(hcsp.HCSPInfo(name, hp))

    return infos

def parse_module_file(text):
    """Parse a file in module format.
    
    Input is the string of the file. Output is a list of pairs (name, hp).

    """
    # Preprocessing: just remove comments
    text_lines = text.strip().split('\n')
    text = ""

    for line in text_lines:
        comment_pos = line.find('#')
        if comment_pos != -1:
            line = line[:comment_pos]
        if line.strip() != "":
            text += line + '\n'

    try:
        decls = decls_parser.parse(text)
        infos = decls.generateHCSPInfo()
    except (exceptions.UnexpectedToken, exceptions.UnexpectedCharacters) as e:
        error_str = "Unable to parse\n"
        for i, line in enumerate(text.split('\n')):
            error_str += line + '\n'
            if i == e.line - 1:
                error_str += " " * (e.column-1) + "^" + '\n'
        raise ParseFileException(error_str)
    except module.ModuleException as e:
        raise ParseFileException("Module exception\n" + e.error_msg)

    return infos
