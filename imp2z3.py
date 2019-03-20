import sys
from imp_interp.imp_parser import *
from imp_interp.imp_lexer import *

def main(args):

    if len(args) != 3:
        print("Usage: python imp2z3.py <input filepath> <output filepath>")
        sys.exit(1)

    ast = generateAST(args[1])
    if not ast:
        sys.stderr.write("File could not be parsed")
        sys.exit(1)

    vars = set({})
    ast.getVars(vars)
    vars = sorted(vars)
    print(vars)
    labels = {'L?'}
    ast.assignLabels(labels)
    labels = sorted(labels)
    print(labels)



def generateAST(filepath):
    imp_text = open(filepath).read()
    tokens = imp_lex(imp_text)
    result = imp_parse(tokens)
    if not result:
        return None
    return result.value


if __name__ == '__main__':
    main(sys.argv)
