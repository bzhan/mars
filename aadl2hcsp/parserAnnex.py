"""Parse an AADL model with Behaviour Annex."""

import re
import json
import ply.lex as lex
import ply.yacc as yacc
import warnings

from ss2hcsp.hcsp.expr import *
from ss2hcsp.hcsp.hcsp import *

warnings.filterwarnings("ignore")

class AnnexParser(object):
    def __init__(self):
        self.Annexs = {}
        self.HCSP = ""

    def getAnnex(self, doc):
        with open(doc, 'r') as f:
            data = f.readlines()
        flag = 0
        i = 0
        while i < len(data):
            line = data[i].strip()
            words = [w.strip() for w in line.split()]
            if 'end' in [w.lower() for w in words]:
                flag = 0
            if flag == 0:
                if 'thread' in [w.lower() for w in words] and 'implementation' in [w.lower() for w in words]:
                    name = words[-1].split('.')[0]
                    flag = 1
                elif 'subprogram' in [w.lower() for w in words]:
                    name = words[-1]
                    flag = 1

            elif 'annex' in [w.lower() for w in words] and flag == 1:
                self.Annexs[name] = {}
                annex_cont = []
                flag = 2

            elif flag == 2:
                if '**};' in words:
                    self.Annexs[name]['Discrete'] = annex_cont
                    flag = 1
                else:
                    annex_cont.append(line)
            i += 1

        return self.Annexs

    def createHCSP(self, state, trans):
        hcsp=[]
        for s in state.keys():
            if 'INITIAL' in state[s] or 'initial' in state[s]:
                now_state=s
                next_state=trans[s]['distination']
                hcsp.extend(trans[s]['content'])
                break

        while 'FINAL' not in state[now_state] and 'final' not in state[now_state]:
            now_state = next_state
            next_state = trans[s]['distination']
            hcsp.extend(trans[s]['content'])

        return hcsp


    def createParser(self, code):
        var=[]
        state={}
        trans={}

        reserved = {
            'transitions': 'TRANSITIONS',
            'states': 'STATES',
            'variables': 'VARIABLES',
            'initial': 'INITIAL',
            'complete': 'COMPLETE',
            'final': 'FINAL',
            'state': 'STATE',
            'int':'INT',
            'float': 'FLOAT',
            'boolean': 'BOOLEAN',
            'dispatch': 'DISPATCH',
            'on':'ON',
            'if':'IF',
            'elsif':'ELIF',
            'else':'ELSE',
            'while': 'WHILE',
            'end': 'END',
            'for': 'FOR',
            'in': 'IN',
            'computation':  'COMPUTATION',
            'ms': 'TIME_MS'
        }
        tokens = ['NAME',
                  'NUMBER',
                  'ATTACHED',
                  'RIGHT_CURLY_BRA',
                  'LEFT_CURLY_BRA',
                  'COMP_OP',
                  'LEFT_ANGLE_BRA',
                  'RIGHT_ANGLE_BRA',
                  'EQUALS',
                  'PLUS',
                  'MINUS',
                  'TIMES',
                  'DIVIDE',
                  'REMAINDER',
                  'LEFT_DIS',
                  'RIGHT_DIS',
                  'RANGE'
        ]
        tokens = tokens + list(reserved.values())
        literals = [ '(',')',',',':',';','!']
        # Tokens
        t_EQUALS = r'='
        t_PLUS = r'\+'
        t_MINUS = r'-'
        t_TIMES = r'\*'
        t_DIVIDE = r'/'
        t_REMAINDER = r'%'
        t_ATTACHED=r':='
        t_LEFT_CURLY_BRA=r'\{'
        t_RIGHT_CURLY_BRA = r'}'
        t_LEFT_ANGLE_BRA = r'<'
        t_RIGHT_ANGLE_BRA = r'>'
        t_NUMBER = r'(-)?\d+(\.\d+)?'
        t_LEFT_DIS=r'-\['
        t_RIGHT_DIS=r']->'
        t_RANGE = r'\...'


        def t_COMP_OP(t):
            r'==|>=|<=|<>'
            return t

        def t_NAME(t):
            r'[_A-Za-z]([_0-9A-Za-z]|::)*'
            t.type = reserved.get(t.value, 'NAME')  # Check for reserved words
            return t

        t_ignore = " \t"
        def t_newline(t):
            r'\n+'
            t.lexer.lineno += t.value.count("\n")

        def t_error(t):
            print("Illegal character '%s'" % t.value[0])
            t.lexer.skip(1)
        # Build the lexer
        lex.lex()
        # Parsing rules
        def p_statement_list(p):
            """ statement : statement statement  """
            if isinstance(p[1], list):
                p1 = p[1]
            elif isinstance(p[1], HCSP):
                p1 = [p[1]]
            else:
                p1 = []
            if isinstance(p[2], list):
                p2 = p[2]
            elif isinstance(p[2], HCSP):
                p2 = [p[2]]
            else:
                p2 = []

            p[0] = p1+p2


        def p_statement_assign(p):
            'statement : NAME ATTACHED expression ";" '
            p[0]= Assign(str(p[1]), p[3])

        def p_statement_expr(p):
            """statement : expression ';' """
            p[0] = p[1]

        def p_expression_binop(p):
            '''expression : expression PLUS expression
                          | expression MINUS expression
                          | expression  TIMES expression
                          | expression DIVIDE expression
                          | expression REMAINDER expression
                          | expression EQUALS expression
                          | expression LEFT_ANGLE_BRA expression
                          | expression RIGHT_ANGLE_BRA expression
                          | expression COMP_OP expression '''
            if p[2] == '+':
                p[0] = PlusExpr(['+', '+'], [p[1], p[3]])
            elif p[2] == '-':
                p[0] = PlusExpr(['+', '-'], [p[1], p[3]])
            elif p[2] == '*':
                p[0] = TimesExpr(['*', '*'], [p[1], p[3]])
            elif p[2] == '\\':
                p[0] = TimesExpr(['*', '\\'], [p[1], p[3]])
            elif p[2]=='%':
                p[0] = TimesExpr(['*', '%'], [p[1], p[3]])
            elif p[2]=='=':
                p[0] = RelExpr('=', p[1], p[3])
            elif p[2] == '>':
                p[0] = RelExpr('>', p[1], p[3])
            elif p[2] == '<':
                p[0] = RelExpr('<', p[1], p[3])
            elif p[2]=='==':
                p[0] = RelExpr('==', p[1], p[3])
            elif p[2] == '!=':
                p[0] = RelExpr('!=', p[1], p[3])
            elif p[2]=='>=':
                p[0] = RelExpr('>=', p[1], p[3])
            elif p[2]=='<=':
                p[0] = RelExpr('<=', p[1], p[3])


        def p_expression_boolean(p):
            """statement : '!' expression ';' """
            p[0] = Assign(str(p[1]), AVar(str(p[1])))

        def p_expression_group(p):
            "expression : '(' expression ')'"
            p[0] = p[2]

        def p_expression_number(p):
            "expression : NUMBER "
            p[0] = AConst(float(p[1]))
        def p_expression_name(p):
            "expression : NAME "
            p[0] = AVar(p[1])

        def p_expression_namelist(p):
            "expression : expression ',' expression"
            p[0]=[]
            if isinstance(p[1], AVar):
                p[0].append(str(p[1]))
            elif isinstance(p[1], list):
                p[0].append(v for v in p[1])

            if isinstance(p[3], AVar):
                p[0].append(str(p[3]))
            elif isinstance(p[3], list):
                p[0].append(v for v in p[3])

        def p_type_data(p):
            """type : INT
                   | FLOAT
                   | BOOLEAN
                   """
            p[0]= 'type'

        def p_define_variable(p):
            """statement : VARIABLES expression ':' type ';'
                          | VARIABLES ':' expression ';'  """
            if len(p)==5:
                x=p[3]
            else:
                x=p[2]
            if isinstance(x, AVar):
                var.append(str(x))
            elif isinstance(x, list):
                for v in x:
                    var.append(v)

        def p_state_list(p):
            """ state_var : state_var state_var
                           | INITIAL
                           | COMPLETE
                           | FINAL"""
            if len(p)== 3:
                p[0]=p[1]+p[2]
            else:
                p[0]=[p[1]]

        def p_time_unit(p):
            """ time_unit : TIME_MS """

        def p_define_state(p):
            """statement : STATES NAME ':' state_var STATE  ';' """
            state[p[2]] = p[4]

        def p_define_transtion(p):
            """statement : TRANSITIONS NAME ':' NAME LEFT_DIS ON DISPATCH RIGHT_DIS NAME LEFT_CURLY_BRA statement RIGHT_CURLY_BRA ';' """
            if isinstance(p[11], list):
                con = [str(hp) for hp in p[11]]
            elif isinstance(p[11], HCSP):
                con = [str(p[11])]
            else:
                con = []
            trans[p[4]]={'distination':p[9], 'content': con}


        def p_if_substatement(p):
            """ if_statement : IF '(' expression ')' statement  """
            if isinstance(p[5], HCSP):
                p[0] =[[p[3], p[5]]]
            elif  isinstance(p[5], list):
                p[0] = [[p[3], Sequence(*p[5])]]

        def p_else_substatement(p):
            """ else_statement : ELSE statement """
            if isinstance(p[2],HCSP):
                p[0] =p[2]
            elif  isinstance(p[2],list):
                p[0] = Sequence(*p[2])

        def p_elif_substatement(p):
            """ elif_statement : ELIF  '(' expression ')' statement
                                | elif_statement elif_statement    """
            if len(p)==3:
                p[0]=p[1]+[3]
            else:
                if isinstance(p[5], HCSP):
                    p[0] = [[p[3], p[5]]]
                elif isinstance(p[5], list):
                    p[0] = [[p[3], Sequence(*p[5])]]

        def p_if_statement(p):
            """ statement : if_statement END IF ';'
                          | if_statement else_statement END IF ';'
                          | if_statement elif_statement else_statement END IF ';' """
            if len(p)== 5:
                p[0] = Condition(p[1][0][0], p[1][0][1])
            elif len(p)== 6:
                p[0] = ITE(p[1], p[2])
            else:
                p[0] = ITE(p[1]+p[2], p[3])

        def p_while_statement(p):
            """ statement :  WHILE '(' expression ')' statement  END WHILE ';' """
            p[0] = Loop(Condition(p[3], p[5]))

        def p_for_statement(p):
            """ statememt : FOR '(' expression IN expression RANGE expression ')' LEFT_CURLY_BRA statement RIGHT_CURLY_BRA ';' """

            init = Assign(str(p[3]), p[5])
            final = RelExpr('<=', p[3], p[7])
            cur = Assign(str(p[3]), PlusExpr(['+', '+'], [p[3], AConst(1)]))
            p[0] = Sequence(init, Loop(Sequence(p[10], cur), final))

        def p_computaion_statement(p):
            """ statement : COMPUTATION '(' expression time_unit ')' ';' """
            p[0] = Wait(AConst(p[3].value*0.001))

        def p_communication_statement(p):
            """ statement : expression '!' ';'
                           | expression '!' '(' expression ',' expression ')' ';' """
            if len(p)== 4:
                p[0] = OutputChannel(str(p[1]))
            else:
                p[0] = Sequence(OutputChannel(str(p[1])+'_out', p[4]),
                                InputChannel(str(p[1])+'_in', str(p[6])))

        def p_error(p):
            if p:
                print("Syntax error at '%s'" % p.value)
            else:
                print("Syntax error at EOF")

        yacc.yacc()
        yacc.parse(code)

        return var, state, trans


if __name__=='__main__':
    file= '../Examples/AADL/isolette/asd.aadl'
    AP=AnnexParser()
    Annexs=AP.getAnnex(file)
    HP={}
    for th in Annexs.keys():
        HP[th] = {}
        if isinstance(Annexs[th]['Discrete'], list):
            code = ' '.join(Annexs[th]['Discrete'])
            var, state, trans = AP.createParser(code)
            HP[th]['Discrete'] = str(AP.createHCSP(state, trans))
    print(HP)






