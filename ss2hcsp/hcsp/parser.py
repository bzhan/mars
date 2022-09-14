"""Parser for expressions."""

from lark import Lark, Transformer, v_args, exceptions
from lark.tree import Meta
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import assertion, label
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import module
from decimal import Decimal


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
        | "true" -> true_cond
        | "false" -> false_cond
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

    ?if_expr: "if" expr "then" if_expr "else" if_expr       // priority 40
        | plus_expr

    ?rel_expr: if_expr "==" if_expr -> eq_cond         // priority 50
        | if_expr "!=" if_expr -> ineq_cond
        | if_expr "<=" if_expr -> less_eq_cond
        | if_expr "<" if_expr -> less_cond
        | if_expr ">=" if_expr -> greater_eq_cond
        | if_expr ">" if_expr -> greater_cond
        | if_expr

    ?neg_expr: "!" neg_expr -> not_cond          // priority 40
        | rel_expr

    ?conj: neg_expr "&&" conj | neg_expr         // Conjunction: priority 35

    ?disj: conj "||" disj | conj                 // Disjunction: priority 30

    ?equiv: disj "<->" equiv | disj             // Equivalent: priority 25

    ?imp: equiv "->" imp | equiv                  // Implies: priority 20

    ?quant: "\\exists" CNAME "." quant                         -> exists_expr  // priority 10
        | "\\exists" "{" CNAME ("," CNAME)+ "}" "." quant      -> exists_expr
        | "\\forall" CNAME "." quant                       -> forall_expr
        | "\\forall" "{" CNAME ("," CNAME)+ "}" "." quant  -> forall_expr
        | imp

    ?expr: quant

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

    ?atom_cmd: "@" CNAME ";" -> var_cmd
        | "skip" ";" -> skip_cmd
        | "wait" "(" expr ")" ";" -> wait_cmd
        | lname ":=" expr ";" -> assign_cmd
        | "(" lname ("," lname)* ")" ":=" expr ";" -> multi_assign_cmd
        | lname ":=" "*" "(" expr ")" ";" -> random_assign_cmd
        | "assert" "(" expr ("," expr)* ")" ";" -> assert_cmd
        | "test" "(" expr ("," expr)* ")" ";" -> test_cmd
        | "log" "(" expr ("," expr)* ")" ";" -> log_cmd
        | comm_cmd ";"
        | "{" cmd "}" "*" maybe_loop_invariant -> repeat_cmd
        | "{" cmd "}" "*" "(" expr ")" maybe_loop_invariant -> repeat_cond_cmd
        | "{" ode_seq "&" expr "}" maybe_ode_invariant -> ode
        | "{" ode_seq "&" expr "}" sln_rule ";" -> ode_sln
        | "{" "&" expr "}" "|>" "[]" "(" interrupt ")" maybe_ode_invariant -> ode_comm_const
        | "{" ode_seq "&" expr "}" "|>" "[]" "(" interrupt ")" maybe_ode_invariant -> ode_comm
        | "if" "(" expr ")" "{" cmd "}" ("else" "if" "(" expr ")" "{" cmd "}")* ("else" "{" cmd "}")? -> ite_cmd
        | "{" cmd "}" -> paren_cmd

    ?maybe_loop_invariant: ("invariant" ord_assertion+ ";")? -> maybe_loop_invariant

    ?ord_assertion: "[" expr "]" maybe_proof_methods          -> ord_assertion
    
    ?maybe_proof_methods: ("{{" proof_method ("," proof_method)* "}}")?    ->maybe_proof_methods
    ?proof_method: (label ":")? method   -> proof_method 
    
    ?label_category: "init"     -> label_categ_init
        | "maintain"            -> label_categ_maintain
        | "init_all"            -> label_categ_init_all

    ?categ_label: label_category     -> categ_label

    ?atom_label: INT
        | "exec"          -> atom_label_exec
        | "skip"             -> atom_label_skip

    ?branch_label: atom_label                 -> atom_label
        | branch_label ("." branch_label)+           -> seq_label
        | atom_label "(" branch_label ")"     -> nest_label

    ?label: categ_label                  
        | branch_label
        | categ_label branch_label       -> comp_label
    
    ?method: "z3"        -> method_z3
      | "wolfram"        -> method_wolfram

    ?maybe_ode_invariant: ("invariant" ode_invariant+ ";")? -> maybe_ode_invariant

    ?ode_invariant: "[" expr "]" ("{" ode_inv_rule expr? "}")? maybe_proof_methods -> ode_invariant
      | "ghost" CNAME "(" CNAME "=" expr ")" -> ghost_intro

    ?ode_inv_rule: "di" -> inv_rule_di
      | "dbx" -> inv_rule_dbx
      | "bc" -> inv_rule_bc

    ?sln_rule: "solution" -> ode_rule_sln

    ?ichoice_cmd: atom_cmd ("++" atom_cmd)*  // Priority: 80

    ?seq_cmd: ichoice_cmd*  // Priority: 70

    ?select_cmd: seq_cmd | comm_cmd "-->" seq_cmd ("$" comm_cmd "-->" seq_cmd)*  // Priority 50

    ?cmd: select_cmd

    ?function_decl: "function" CNAME "(" CNAME ("," CNAME)* ")" "=" expr ";"

    ?hoare_pre : "pre" (ord_assertion)* ";" -> hoare_pre
    ?hoare_post : "post" (ord_assertion)* ";" -> hoare_post
    ?hoare_triple: (function_decl)* hoare_pre cmd hoare_post

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

    COMMENT: /#.*/ | /\/\*+([\s\S]*?)\*\//

    %ignore WS
    %ignore COMMENT
"""

def _vargs_meta_inline(f, _data, children, meta):
    return f(meta, *children)

@v_args(wrapper=_vargs_meta_inline)
class HPTransformer(Transformer):
    def __init__(self):
        pass

    def var_expr(self, meta, s):
        return expr.AVar(str(s), meta=meta)

    def num_expr(self, meta, v):
        return expr.AConst(Decimal(str(v)) if '.' in v or 'e' in v else int(v), meta=meta)

    def string_expr(self, meta, s):
        return expr.AConst(str(s)[1:-1], meta=meta)  # remove quotes

    def empty_list(self, meta):
        return expr.ListExpr(meta=meta)

    def literal_list(self, meta, *args):
        if all(isinstance(arg, expr.AConst) for arg in args):
            return expr.AConst(list(arg.value for arg in args), meta=meta)
        else:
            return expr.ListExpr(*args, meta=meta)

    def empty_dict(self, meta):
        return expr.DictExpr(meta=meta)

    def literal_dict(self, meta, *args):
        # args should contain 2*n elements, which are key-value pairs
        assert len(args) >= 2 and len(args) % 2 == 0
        pairs = []
        for i in range(0,len(args),2):
            pairs.append((str(args[i]), args[i+1]))
        return expr.DictExpr(*pairs, meta=meta)

    def array_idx_expr(self, meta, a, i):
        return expr.ArrayIdxExpr(expr.AVar(str(a)), i, meta=meta)
    
    def array_idx_expr2(self, meta, a, i, j):
        return expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.AVar(str(a)), i, meta=meta), j, meta=meta)

    def array_idx_expr3(self, meta, a, i, j, k):
        return expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.AVar(str(a)), i, meta=meta), j, meta=meta), k, meta=meta)

    def field_array_idx(self, meta, e, field, i):
        return expr.ArrayIdxExpr(expr.FieldNameExpr(e, field, meta=meta), i, meta=meta)

    def field_expr(self, meta, e, field):
        return expr.FieldNameExpr(e, field, meta=meta)

    def if_expr(self, meta, cond, e1, e2):
        return expr.IfExpr(cond, e1, e2, meta=meta)

    def exists_expr(self, meta, *args):
        # The last arg is the expression, other args are variables.
        assert len(args) >= 2
        e = args[-1]
        if len(args) == 2:
            return expr.ExistsExpr(str(args[0]), e, meta=meta)
        else:
            return expr.ExistsExpr(list(str(arg) for arg in args[:-1]), e, meta=meta)

    def forall_expr(self, meta, *args):
        # The last arg is the expression, other args are variables.
        assert len(args) >= 2
        e = args[-1]
        if len(args) == 2:
            return expr.ForAllExpr(str(args[0]), e, meta=meta)
        else:
            return expr.ForAllExpr(list(str(arg) for arg in args[:-1]), e, meta=meta)

    def plus_expr(self, meta, e1, e2):
        return expr.OpExpr("+", e1, e2, meta=meta)

    def minus_expr(self, meta, e1, e2):
        return expr.OpExpr("-", e1, e2, meta=meta)

    def uminus(self, meta, e):
        return expr.OpExpr("-", e, meta=meta)

    def times_expr(self, meta, e1, e2):
        return expr.OpExpr("*", e1, e2, meta=meta)

    def divide_expr(self, meta, e1, e2):
        return expr.OpExpr("/", e1, e2, meta=meta)

    def power_expr(self, meta, e1, e2):
        return expr.OpExpr("^", e1, e2, meta=meta)

    def min_expr(self, meta, e1, e2):
        return expr.FunExpr("min", [e1, e2], meta=meta)

    def max_expr(self, meta, e1, e2):
        return expr.FunExpr("max", [e1, e2], meta=meta)

    def mod_expr(self, meta, e1, e2):
        return expr.OpExpr("%", e1, e2, meta=meta)

    def gcd_expr(self, meta, *exprs):
        return expr.FunExpr(fun_name="gcd", exprs=exprs, meta=meta)

    def fun_expr(self, meta, fun_name, *exprs):
        return expr.FunExpr(str(fun_name), exprs, meta=meta)

    def eq_cond(self, meta, e1, e2):
        return expr.RelExpr("==", e1, e2, meta=meta)

    def ineq_cond(self, meta, e1, e2):
        return expr.RelExpr("!=", e1, e2, meta=meta)

    def less_eq_cond(self, meta, e1, e2):
        return expr.RelExpr("<=", e1, e2, meta=meta)

    def less_cond(self, meta, e1, e2):
        return expr.RelExpr("<", e1, e2, meta=meta)

    def greater_eq_cond(self, meta, e1, e2):
        return expr.RelExpr(">=", e1, e2, meta=meta)

    def greater_cond(self, meta, e1, e2):
        return expr.RelExpr(">", e1, e2, meta=meta)

    def not_cond(self, meta, e):
        return expr.LogicExpr("!", e, meta=meta)

    def true_cond(self, meta):
        return expr.BConst(True, meta=meta)

    def false_cond(self, meta):
        return expr.BConst(False, meta=meta)

    def conj(self, meta, b1, b2):
        return expr.LogicExpr("&&", b1, b2, meta=meta)

    def disj(self, meta, b1, b2):
        return expr.LogicExpr("||", b1, b2, meta=meta)

    def imp(self, meta, b1, b2):
        return expr.LogicExpr("->", b1, b2, meta=meta)

    def equiv(self, meta, b1, b2):
        return expr.LogicExpr("<->", b1, b2, meta=meta)

    def var_cmd(self, meta, name):
        return hcsp.Var(str(name), meta=meta)

    def skip_cmd(self, meta):
        return hcsp.Skip(meta=meta)

    def wait_cmd(self, meta, delay):
        return hcsp.Wait(delay, meta=meta)

    def assign_cmd(self, meta, var, expr):
        return hcsp.Assign(var, expr, meta=meta)

    def multi_assign_cmd(self, meta, *args):
        return hcsp.Assign(args[:-1], args[-1], meta=meta)

    def random_assign_cmd(self, meta, var, cond):
        return hcsp.RandomAssign(var, cond, meta=meta)

    def assert_cmd(self, meta, *args):
        # First argument is the assert condition. The remaining ones
        # are error messages. 
        bexpr, msgs = args[0], args[1:]
        return hcsp.Assert(bexpr, msgs, meta=meta)

    def test_cmd(self, meta, *args):
        # First argument is the test condition. The remaining ones
        # are warning messages.
        bexpr, msgs = args[0], args[1:]
        return hcsp.Test(bexpr, msgs, meta=meta)

    def log_cmd(self, meta, *args):
        return hcsp.Log(args[0], exprs=args[1:], meta=meta)

    def seq_cmd(self, meta, *args):
        if len(args) == 0:
            return hcsp.Skip(meta=meta)
        elif len(args) == 1:
            return args[0]
        else:
            return hcsp.Sequence(*args, meta=meta)

    def input_cmd(self, meta, *args):
        # First argument is channel name, last argument is variable name.
        # Middle arguments are args to channel name.
        ch_name, ch_args, var_name = args[0], args[1:-1], args[-1]
        return hcsp.InputChannel(hcsp.Channel(str(ch_name), ch_args, meta=meta), var_name, meta=meta)

    def input_none_cmd(self, meta, *args):
        # First argument is channel name, remaining arguments are its args.
        ch_name, ch_args = args[0], args[1:]
        return hcsp.InputChannel(hcsp.Channel(str(ch_name), ch_args, meta=meta), meta=meta)

    def output_cmd(self, meta, *args):
        # First argument is channel name, last argument is variable name.
        # Middle arguments are args to channel name.
        ch_name, ch_args, expr = args[0], args[1:-1], args[-1]
        return hcsp.OutputChannel(hcsp.Channel(str(ch_name), ch_args, meta=meta), expr, meta=meta)

    def output_none_cmd(self, meta, *args):
        # First argument is channel name, remaining arguments are its args.
        ch_name, ch_args = args[0], args[1:]
        return hcsp.OutputChannel(hcsp.Channel(str(ch_name), ch_args, meta=meta), meta=meta)

    def ord_assertion(self, meta, expr, proof_methods):
        return assertion.OrdinaryAssertion(expr=expr, proof_methods=proof_methods, meta=meta)

    def maybe_loop_invariant(self, meta, *args):
        return args

    def maybe_ode_invariant(self, meta, *args):
        return args

    def ode_invariant(self, meta, *args):
        if len(args) == 2:
            return assertion.CutInvariant(expr=args[0], proof_methods=args[-1], meta=meta)
        elif len(args) == 3:
            return assertion.CutInvariant(expr=args[0], rule=args[1], proof_methods=args[-1], meta=meta)
        else:
            return assertion.CutInvariant(expr=args[0], rule=args[1], rule_arg=args[2], proof_methods=args[-1], meta=meta)
    
    def ghost_intro(self, meta, var, var_dot, diff):
        assert var_dot.endswith("_dot")
        assert var == var_dot[:-4]
        return assertion.GhostIntro(var=var, diff=diff, meta=meta)

    def inv_rule_di(self, meta): return "di"
    def inv_rule_bc(self, meta): return "bc"
    def inv_rule_dbx(self, meta): return "dbx"

    def ode_rule_dw(self, meta): return "dw"
    def ode_rule_sln(self, meta): return "solution"

    def method_z3(self, meta): return "z3"
    def method_wolfram(self, meta): return "wolfram"

    def label_categ_init(self, meta): return "init"
    def label_categ_maintain(self, meta): return "maintain"
    def label_categ_init_all(self, meta): return "init_all"

    def atom_label_exec(self, meta): return "exec"
    def atom_label_skip(self, meta): return "skip"

    def atom_label(self, meta, value):
        return label.AtomLabel(value=value)

    def seq_label(self, meta, *args):
        return label.SequenceLabel(*args)

    def nest_label(self, meta, value, sub_label):
        return label.NestLabel(value=value, sub_label=sub_label)

    def categ_label(self, meta, categ):
        return label.CategLabel(categ=categ)

    def comp_label(self, meta, categ_label, branch_label):
        return label.CompLabel(categ_label=categ_label, branch_label=branch_label)

    def proof_method(self, meta, *args):
        assert(len(args) == 1 or len(args) == 2)
        if len(args) == 1:
            return assertion.ProofMethod(method=args[0], meta=meta)
        else:
            return assertion.ProofMethod(label=args[0], method=args[1], meta=meta)

    def maybe_proof_methods(self, meta, *args):
        if len(args) == 0:
            return assertion.ProofMethods(meta=meta)
        else:
            return assertion.ProofMethods(*args, meta=meta)
            
    def repeat_cmd(self, meta, cmd, inv):
        return hcsp.Loop(cmd, meta=meta, inv=inv)

    def repeat_cond_cmd(self, meta, cmd, cond, inv):
        return hcsp.Loop(cmd, constraint=cond, meta=meta, inv=inv)

    def ode_seq(self, meta, *args):
        res = []
        for i in range(0,len(args),2):
            assert args[i].endswith("_dot")
            res.append((str(args[i][:-4]), args[i+1]))
        return res

    def interrupt(self, meta, *args):
        res = []
        for i in range(0, len(args), 2):
            res.append((args[i], args[i+1]))
        return res

    def ode(self, meta, eqs, constraint, asts):
        ghosts = []
        inv = []
        for ast in asts:
            if isinstance(ast, assertion.GhostIntro):
                ghosts.append(ast)
            elif isinstance(ast, assertion.CutInvariant):
                inv.append(ast)
            else:
                raise NotImplementedError
        return hcsp.ODE(eqs, constraint, meta=meta, ghosts=tuple(ghosts), inv=tuple(inv))

    def ode_sln(self, meta, eqs, constraint, rule):
        return hcsp.ODE(eqs, constraint, meta=meta, rule=rule)

    def ode_comm_const(self, meta, constraint, io_comms, inv):
        return hcsp.ODE_Comm([], constraint, io_comms, meta=meta)

    def ode_comm(self, meta, eqs, constraint, io_comms, inv):
        return hcsp.ODE_Comm(eqs, constraint, io_comms, meta=meta)

    def ichoice_cmd(self, meta, *args):
        if len(args) == 1:
            return args[0]
        else:
            return hcsp.IChoice(*args, meta=meta)

    def select_cmd(self, meta, *args):
        assert len(args) % 2 == 0 and len(args) >= 4
        io_comms = []
        for i in range(0, len(args), 2):
            io_comms.append((args[i], args[i+1]))
        return hcsp.SelectComm(*io_comms, meta=meta)

    def ite_cmd(self, meta, *args):
        if_hps = []
        for i in range(0, len(args)//2):
            if_hps.append((args[2*i], args[2*i+1]))
        if len(args) % 2 == 1:
            else_hp = args[-1]
        else:
            else_hp = None
        return hcsp.ITE(if_hps, else_hp, meta=meta)

    def paren_cmd(self, meta, c):
        return c

    def procedure(self, meta, name, hp):
        return hcsp.Procedure(name, hp, meta=meta)

    def parallel_cmd(self, meta, *args):
        if len(args) == 1:
            return args[0]
        else:
            return hcsp.Parallel(*args, meta=meta)

    def function_decl(self, meta, *args):
        name = str(args[0])
        vars = list(str(var) for var in args[1:-1])
        expr = args[-1]
        return hcsp.Function(name, vars, expr)

    def hoare_pre(self, meta, *args):
        return list(args)

    def hoare_post(self, meta, *args):
        return list(args)

    def hoare_triple(self, meta, *args):
        # The last three arguments are pre, hp, and post.
        pre = args[-3]
        hp = args[-2]
        post = args[-1]

        # The other arguments are functions
        functions = dict()
        for item in args[:-3]:
            assert isinstance(item, hcsp.Function);
            functions[item.name] = item
        return hcsp.HoareTriple(pre, hp, post, functions=functions, meta=meta)

    def module_sig(self, meta, *args):
        return tuple(str(arg) for arg in args)

    def module_output(self, meta, *args):
        return tuple(str(arg) for arg in args)

    def module(self, meta, *args):
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
        return module.HCSPModule(name, code, params=params, outputs=outputs, procedures=procedures, meta=meta)

    def module_arg_channel(self, meta, *args):
        # First argument is channel name, remaining arguments are channel args.
        ch_name, ch_args = args[0], args[1:]
        return hcsp.Channel(str(ch_name), tuple(expr.AConst(ch_arg, meta=meta) for ch_arg in ch_args), meta=meta)

    def module_arg_expr(self, meta, expr):
        return expr

    def module_args(self, meta, *args):
        return args

    def module_inst(self, meta, name, sig):
        return module.HCSPModuleInst(name, sig[0], sig[1:], meta=meta)
    
    def module_inst_noname(self, meta, sig):
        return module.HCSPModuleInst(sig[0], sig[0], sig[1:], meta=meta)

    def hcsp_import(self, meta, filename):
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

    def system(self, meta, *args):
        # Each item is a module instantiation
        return module.HCSPSystem(args, meta=meta)

    def decls(self, meta, *args):
        # A list of declarations.
        return module.HCSPDeclarations(args, meta=meta)

hp_transformer = HPTransformer()

expr_parser = Lark(grammar, start="expr", parser="lalr", transformer=hp_transformer)
hp_parser = Lark(grammar, start="parallel_cmd", parser="lalr", transformer=hp_transformer)
module_parser = Lark(grammar, start="module", parser="lalr", transformer=hp_transformer)
system_parser = Lark(grammar, start="system", parser="lalr", transformer=hp_transformer)
decls_parser = Lark(grammar, start="decls", parser="lalr", transformer=hp_transformer)

# Variants of the parsers without internal transformer, returning a Lark Tree instead of a HCSP expression.
# They allow us to get meta information about line and character numbers of the parsed code.
expr_tree_parser = Lark(grammar, start="expr", parser="lalr", propagate_positions=True)
hp_tree_parser = Lark(grammar, start="parallel_cmd", parser="lalr", propagate_positions=True)
hoare_triple_tree_parser = Lark(grammar, start="hoare_triple", parser="lalr", propagate_positions=True)
module_tree_parser = Lark(grammar, start="module", parser="lalr", propagate_positions=True)
system_tree_parser = Lark(grammar, start="system", parser="lalr", propagate_positions=True)
decls_tree_parser = Lark(grammar, start="decls", parser="lalr", propagate_positions=True)

def parse_expr_with_meta(text): return hp_transformer.transform(expr_tree_parser.parse(text))
def parse_hp_with_meta(text): return hp_transformer.transform(hp_tree_parser.parse(text))
def parse_hoare_triple_with_meta(text): return hp_transformer.transform(hoare_triple_tree_parser.parse(text))
def parse_module_with_meta(text): return hp_transformer.transform(module_tree_parser.parse(text))
def parse_system_with_meta(text): return hp_transformer.transform(system_tree_parser.parse(text))
def parse_decls_with_meta(text): return hp_transformer.transform(decls_tree_parser.parse(text))


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
