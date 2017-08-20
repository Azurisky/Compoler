import sys
sys.path.insert(0, "..")

tokens = (
    'NAME', 'NUMBER', 'PRINT'
)

literals = ['=', '+', '-', '*', '/']

# Tokens
t_PRINT = r'print'
t_NAME  = r'\b((?!print)[a-zA-Z_][a-zA-Z0-9_]*)+\b'


def t_NUMBER(t):
    r'\d+'
    t.value = int(t.value)
    return t

t_ignore = " \t"

def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")

def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

# Build the lexer
import ply.lex as lex
lex.lex()

# Parsing rules

precedence = (
    ('left', '+', '-'),
    ('left', '*', '/'),
)

# dictionary of names
names = {}

# Statement
def p_statement_assign(p):
    'statement : NAME "=" expression'
    names[p[1]] = p[3]

def p_statement_print(p):
    'statement : PRINT expression'
    print(p[2])

def p_statement_again(p):
    'statement : statement statement'

# Expression
def p_expression_binop(p):
    '''expression : expression '+' expression
                  | expression '-' expression
                  | expression '*' expression
                  | expression '/' expression'''
    if p[2] == '+':
        p[0] = p[1] + p[3]
    elif p[2] == '-':
        p[0] = p[1] - p[3]
    elif p[2] == '*':
        p[0] = p[1] * p[3]
    elif p[2] == '/':
        p[0] = p[1] / p[3]

def p_expression_number(p):
    "expression : NUMBER"
    p[0] = p[1]

def p_expression_name(p):
    "expression : NAME"
    try:
        p[0] = names[p[1]]
    except LookupError:
        print("Undefined name '%s'" % p[1])
        p[0] = 0

def p_error(p):
    if p:
        print("Syntax error at '%s'" % p.value)
    else:
        print("Syntax error at EOF")

import ply.yacc as yacc
yacc.yacc()


f = open('ex1.py','r')
yacc.parse(f.read())
