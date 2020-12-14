"""Parser for expressions."""

from lark import Lark, Transformer, v_args, exceptions
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import module


grammar = r"""
    ?atom_expr: CNAME -> var_expr
        | SIGNED_NUMBER -> num_expr
        | ESCAPED_STRING -> string_expr
        | "[]" -> empty_list
        | "[" expr ("," expr)* "]" -> literal_list
        | atom_expr "[" expr "]" -> array_idx_expr
        | "min" "(" expr "," expr ")" -> min_expr
        | "max" "(" expr "," expr ")" -> max_expr
        | "gcd" "(" expr ("," expr)+ ")" -> gcd_expr
        | CNAME "(" expr ("," expr)* ")" -> fun_expr
        | "(" expr ")"

    ?times_expr: times_expr "*" atom_expr -> times_expr
        | times_expr "/" atom_expr -> divide_expr
        | times_expr "%" atom_expr -> mod_expr
        | atom_expr

    ?plus_expr: plus_expr "+" times_expr -> plus_expr
        | plus_expr "-" times_expr -> minus_expr
        | "-" times_expr -> uminus_expr
        | times_expr

    ?expr: plus_expr

    ?atom_cond: expr "==" expr -> eq_cond
        | expr "!=" expr -> ineq_cond
        | expr "<=" expr -> less_eq_cond
        | expr "<" expr -> less_cond
        | expr ">=" expr -> greater_eq_cond
        | expr ">" expr -> greater_cond
        | "~" cond -> not_cond
        | "true" -> true_cond
        | "false" -> false_cond
        | "(" cond ")"
    
    ?conj: atom_cond "&&" conj | atom_cond     // Conjunction: priority 35

    ?disj: conj "||" disj | conj   // Disjunction: priority 30

    ?imp: disj "-->" imp | disj  // Implies: priority 25

    ?cond: imp

    ?comm_cmd: CNAME "?" CNAME -> input_cmd
        | CNAME "?" -> input_none_cmd
        | CNAME "!" expr -> output_cmd
        | CNAME "!" -> output_none_cmd

    ?ode_seq: CNAME "=" expr ("," CNAME "=" expr)*

    ?interrupt: comm_cmd "-->" cmd ("," comm_cmd "-->" cmd)*

    ?atom_cmd: "@" CNAME -> var_cmd
        | "skip" -> skip_cmd
        | "wait" "(" expr ")" -> wait_cmd
        | CNAME ":=" expr -> assign_cmd
        | "(" CNAME ("," CNAME)* ")" ":=" expr -> multi_assign_cmd
        | "assert" "(" cond ")" -> assert_cmd
        | "log" "(" expr ")" -> log_cmd
        | comm_cmd
        | "(" cmd ")**" -> repeat_cmd
        | "(" cmd "){" cond "}**" -> repeat_cond_cmd
        | "<" ode_seq "&" cond ">" -> ode
        | "<" ode_seq "&" cond ">" "|>" "[]" "(" interrupt ")" -> ode_comm
        | "rec" CNAME ".(" cmd ")" -> rec_cmd
        | "if" cond "then" cmd ("elif" cond "then" cmd)* "else" cmd "endif" -> ite_cmd 
        | "(" cmd ")" -> paren_cmd

    ?cond_cmd: atom_cmd | cond "->" atom_cmd       // Priority: 90

    ?seq_cmd: cond_cmd (";" cond_cmd)*  // Priority: 70

    ?select_cmd: seq_cmd | comm_cmd "-->" seq_cmd ("$" comm_cmd "-->" seq_cmd)*  // Priority 50

    ?cmd: select_cmd

    ?parallel_cmd: cmd ("||" cmd)*   // Priority 30, outermost level only

    ?module_sig: CNAME "(" CNAME ("," CNAME)* ")"  -> module_sig
        | CNAME "(" ")"                            -> module_sig

    ?module_output: "output" CNAME ("," CNAME)* ";"    -> module_output
    
    ?module: "module" module_sig ":" (module_output)* "begin" cmd "end" "endmodule"

    ?module_inst: module_sig    -> module_inst_noname
        | CNAME "=" module_sig  -> module_inst

    ?system: "system" module_inst ("||" module_inst)* "endsystem"

    ?decls: (module | system)*

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
        return expr.AConst(float(v) if '.' in v else int(v))

    def string_expr(self, s):
        return expr.AConst(str(s))

    def empty_list(self):
        return expr.AConst(tuple())

    def literal_list(self, *args):
        if all(isinstance(arg, expr.AConst) for arg in args):
            return expr.AConst(tuple(arg.value for arg in args))
        else:
            return expr.ListExpr(*args)

    def array_idx_expr(self, a, i):
        return expr.ArrayIdxExpr(a, i)

    def plus_expr(self, e1, e2):
        signs, exprs = [], []
        if isinstance(e1, expr.PlusExpr):
            signs.extend(e1.signs)
            exprs.extend(e1.exprs)
        else:
            signs.append('+')
            exprs.append(e1)
        if isinstance(e2, expr.PlusExpr):
            signs.extend(e2.signs)
            exprs.extend(e2.exprs)
        else:
            signs.append('+')
            exprs.append(e2)
        return expr.PlusExpr(signs, exprs)

    def minus_expr(self, e1, e2):
        return expr.PlusExpr(["+", "-"], [e1, e2])

    def uminus_expr(self, e):
        return expr.PlusExpr(["-"], [e])

    def times_expr(self, e1, e2):
        return expr.TimesExpr(["*", "*"], [e1, e2])

    def divide_expr(self, e1, e2):
        return expr.TimesExpr(["*", "/"], [e1, e2])

    def min_expr(self, e1, e2):
        return expr.FunExpr("min", [e1, e2])

    def max_expr(self, e1, e2):
        return expr.FunExpr("max", [e1, e2])

    def mod_expr(self, e1, e2):
        return expr.ModExpr(e1, e2)

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
        return hcsp.Assign(str(var), expr)

    def multi_assign_cmd(self, *args):
        return hcsp.Assign((str(arg) for arg in args[:-1]), args[-1])

    def assert_cmd(self, bexpr):
        return hcsp.Assert(bexpr)

    def log_cmd(self, expr):
        return hcsp.Log(expr)

    def seq_cmd(self, *args):
        if len(args) == 1:
            return args[0]
        else:
            return hcsp.Sequence(*args)

    def input_cmd(self, ch_name, var_name):
        return hcsp.InputChannel(str(ch_name), str(var_name))

    def input_none_cmd(self, ch_name):
        return hcsp.InputChannel(str(ch_name))

    def output_cmd(self, ch_name, expr):
        return hcsp.OutputChannel(str(ch_name), expr)

    def output_none_cmd(self, ch_name):
        return hcsp.OutputChannel(str(ch_name))

    def repeat_cmd(self, cmd):
        return hcsp.Loop(cmd)

    def repeat_cond_cmd(self, cmd, cond):
        return hcsp.Loop(cmd, constraint=cond)

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

    def ode_comm(self, eqs, constraint, io_comms):
        return hcsp.ODE_Comm(eqs, constraint, io_comms)

    def cond_cmd(self, cond, cmd):
        return hcsp.Condition(cond=cond, hp=cmd)

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
        # The middle items are the output sequences
        # The last item is code for the module
        assert len(args) >= 2
        sig, outputs, code = args[0], args[1:-1], args[-1]
        if isinstance(sig, tuple):
            name, params = sig[0], sig[1:]
        else:
            name, params = sig, tuple()
        return module.HCSPModule(name, params, outputs, code)

    def module_inst(self, name, sig):
        return module.HCSPModuleInst(name, sig[0], sig[1:])
    
    def module_inst_noname(self, sig):
        return module.HCSPModuleInst(sig[0], sig[0], sig[1:])

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
            line = line[:comment_pos].strip()
        if line.find('::=') != -1:
            lines.append(line)
        else:
            if line != "":
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
            line = line[:comment_pos].strip()
        text += line + '\n'

    try:
        decls = decls_parser.parse(text)
    except (exceptions.UnexpectedToken, exceptions.UnexpectedCharacters) as e:
        error_str = "Unable to parse\n"
        for i, line in enumerate(text.split('\n')):
            error_str += line + '\n'
            if i == e.line - 1:
                error_str += " " * (e.column-1) + "^" + '\n'
        raise ParseFileException(error_str)
        
    return decls.generateHCSPInfo()
