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

    z3_text = generateZ3(ast)

    outFile = open(args[2], "w")
    for line in z3_text:
        outFile.write(line)
        outFile.write("\n")
    outFile.close()



def generateAST(filepath):
    imp_text = open(filepath).read()
    tokens = imp_lex(imp_text)
    result = imp_parse(tokens)
    if not result:
        return None
    return result.value

def generateZ3(ast):
    z3 = []
    # get vars
    vars = set({})
    ast.getVars(vars)
    vars = sorted(vars)

    # get labels
    labels = {'?'}
    ast.assignLabels(labels)
    labels = sorted(labels)

    # define datatypes and lebels
    z3.append(declareDataTypes("Var", vars))
    z3.append(declareDataTypes("Lab", labels))
    z3.append(defineEnEx0(vars))
    z3.append(declareEnAndEx(labels))
    ast.genZ3(z3, "0")
    z3.append("(check-sat)\n")
    z3.append("(get-model)\n")

    return z3

def declareDataTypes(type, names):
    str = "(declare-datatypes () ((" + type
    for name in names:
        str += " "
        if type == "Lab":
            str += "L" + name
        else:
            str += name
    str += ")))\n"
    return str

def defineEnEx0(vars):
    str = "(define-fun En0 ((v!1 Var) (l!1 Lab)) Bool\n(or "
    for var in vars:
        str += "(and (= v!1 " + var + ") (= l!1 L?))\n"
    str += "))\n\n"
    str += "(declare-fun Ex0  (Var Lab) Bool)\n"
    str += "(assert (forall ((v!1 Var) (l!1 Lab))\n(= (Ex0"
    str += " v!1 l!1) (En0 v!1 l!1))))\n"
    return str

def declareEnAndEx(labels):
    str = ""
    for label in labels:
        if label is not "?":
            if int(label) is not 0:
                str += "(declare-fun En" + label
                str += " (Var Lab) Bool)\n"
            str += "(declare-fun Ex" + label + " (Var Lab) Bool)\n"
    return str


if __name__ == '__main__':
    main(sys.argv)
