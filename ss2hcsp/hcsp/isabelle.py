"""Translation from HCSP to Isabelle."""

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp


def getVariableTable(vars):
    """Give one-character name to each variable.

    vars - list(str): list of variable names.

    Returns a dictionary mapping variable names to Isabelle
    definitions. Also return the Isabelle code containing variable
    definitions.

    """
    if len(vars) > 26:
        raise AssertionError('Translate to Isabelle: too many variables')

    init_code = ""
    mapping = dict()
    for i, var in enumerate(vars):
        camelCase = var[0].upper() + var[1:].lower()
        char = chr(97 + i)  # starting from 'a'
        init_code += "definition %s :: char where \"%s = CHR ''%s''\"\n" % (camelCase, camelCase, char)
        mapping[var] = camelCase

    return init_code, mapping

code_pattern = """
theory %s
    imports continuousInv
begin

text \<open>Variables\<close>

%s

text \<open>Processes\<close>

%s

end
"""

def translate_isabelle(process, name):
    """Translate an HCSP process to Isabelle code.

    process - list(HCSPInfo): the parallel process to be translated.
    name - str: process name, to be used as name of the Isabelle file).

    """
    # First, collect all variables
    vars = set()
    for info in process:
        vars = vars.union(info.hp.get_vars())

    init_code, mapping = getVariableTable(vars)

    def trans_expr(e):
        if isinstance(e, expr.AVar):
            return "s %s" % mapping[e.name]
        elif isinstance(e, expr.AConst):
            return str(e.value)
        elif isinstance(e, expr.PlusExpr):
            res = trans_expr(e.exprs[0])
            if e.signs[0] == "-":
                if res.startswith("-") or isinstance(e.exprs[0], expr.PlusExpr):
                    res = "-(" + res + ")"
                else:
                    res = "-" + res
            for sign, e2 in zip(e.signs[1:], e.exprs[1:]):
                trans_e2 = trans_expr(e2)
                if trans_e2.startswith("-") or (sign == "-" and isinstance(e2, expr.PlusExpr)):
                    res += " " + sign + " (" + trans_e2 + ")"
                else:
                    res += " " + sign + " " + trans_e2
            return res
        elif isinstance(e, expr.TimesExpr):
            res = trans_expr(e.exprs[0])
            if isinstance(e.exprs[0], expr.PlusExpr) or (e.signs[0] == "/" and isinstance(e.exprs[0], expr.TimesExpr)):
                res = "(" + res + ")"
            if e.signs[0] == "/":
                res = "1/" + res
            for sign, e2 in zip(e.signs[1:], e.exprs[1:]):
                trans_e2 = trans_expr(e2)
                if isinstance(e2, expr.PlusExpr) or (sign == "/" and isinstance(e2, expr.TimesExpr)) \
                        or (sign == "*" and trans_e2.startswith("-")):
                    res += " " + sign + " (" + trans_e2 + ")"
                else:
                    res += " " + sign + " " + trans_e2
            return res
        elif isinstance(e, expr.BConst):
            return "True" if e.value else "False"
        elif isinstance(e, expr.RelExpr):
            return "%s %s %s" % (trans_expr(e.expr1), e.op, trans_expr(e.expr2))
        elif isinstance(e, expr.FunExpr):
            if e.fun_name in ('sqrt',):
                return "%s(%s)" % (e.fun_name, trans_expr(e.exprs[0]))
            else:
                print(e)
                raise NotImplementedError
        elif isinstance(e, expr.LogicExpr):
            if e.op == '||':
                return "%s \<or> %s" % (trans_expr(e.expr1), trans_expr(e.expr2))
            elif e.op == '&&':
                return "%s \<and> %s" % (trans_expr(e.expr1), trans_expr(e.expr2))
            else:
                raise NotImplementedError
        else:
            print(e, type(e))
            raise NotImplementedError

    def trans_lambda_expr(e):
        if not e.get_vars():
            return "(\<lambda>_. %s)" % trans_expr(e)
        else:
            return "(\<lambda>s. %s)" % trans_expr(e)

    def trans_ode_pair(v, eq):
        return "%s := %s" % (mapping[v], trans_lambda_expr(eq))

    def trans(proc):
        if proc.type == 'assign':
            return "%s ::= %s" % (mapping[proc.var_name.name], trans_lambda_expr(proc.expr))
        elif proc.type == 'sequence':
            return ";\n".join(trans(p) for p in proc.hps)
        elif proc.type == 'loop':
            body = trans(proc.hp)
            indent_body = '\n'.join('  ' + line for line in body.split('\n'))
            return "Rep (\n%s\n)" % indent_body
        elif proc.type == 'output_channel':
            return "Cm (''%s''[!]%s)" % (proc.ch_name, trans_lambda_expr(proc.expr))
        elif proc.type == 'input_channel':
            return "Cm (''%s''[?]%s)" % (proc.ch_name, mapping[proc.var_name.name])
        elif proc.type == 'ite':
            cond, body = proc.if_hps[0]
            body = trans(body)
            indent_body = '\n'.join('  ' + line for line in body.split('\n'))
            if len(proc.if_hps) > 1:
                else_body = trans(hcsp.ITE(proc.if_hps[1:], proc.else_hp))
            else:
                else_body = trans(proc.else_hp)
            indent_else = '\n'.join('  ' + line for line in body.split('\n'))
            return "IF (%s) THEN\n%s\nELSE\n%s\nFI" % (
                trans_lambda_expr(cond), indent_body, indent_else)
        elif proc.type == 'ode':
            return "Cont (ODE ((\<lambda>_ _. 0)(%s))) (%s)" % (
                ', '.join(trans_ode_pair(v, eq) for v, eq in proc.eqs), trans_lambda_expr(proc.constraint))
        else:
            print(proc.type, proc)
            raise NotImplementedError

    proc_code_list = []
    for info in process:
        proc_code = "definition %s :: proc where\n  \"%s =" % (info.name, info.name)
        for line in trans(info.hp).split('\n'):
            proc_code += "\n    " + line
        proc_code += "\"\n"
        proc_code_list.append(proc_code)

    code = code_pattern % (name, init_code, '\n'.join(proc_code for proc_code in proc_code_list))

    return code
