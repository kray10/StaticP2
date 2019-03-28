# StaticP2

#### Authors
Kevin Ray and Johnathan Bliss

## Description
This project uses an existing imp parser (https://github.com/jayconrod/imp-interpreter) to create an abstract syntax tree (AST) for imp code. This AST can then be used to output z3 for the purpose of creating a model for reaching definitions.

## Running imp2z3
The program can be run in following manner:
```
python imp2.z3.py <input file> <output file>
```
The input file should be valid imp code. After running the output file will contain the z3 code. The z3 code will already have check-sat and get-model at the end of the file. Therefore, model can then be obtained by calling:
```
z3 <output file>
```
## Changes

### Modifications to IMP Parser
The imp parser that was used was modified in the following ways.
1. Unneeded functions of the AST were removed, such as the eval function.
2. New functions were added to label all of the commands from the grammar and produce the z3 from the AST.
3. The imp parser did not originally support the "skip" command, so functionality was added to accoutn for that.

### Changes to Project Grammar
The imp parser that was used was already configured to allow for a larger subset of the imp language than the grammar for this project. We decided to leave that functionality in. As a result, the parser will parse, for example, if statements without an else but when it attempts to output the z3 it will fail since the if with no else is not part of the grammar for this project.

The grammar was slightly modified since this parser uses the "end" keyword to denote the stop of while and if statements. Therefore, the modifed grammar would be as follows:

```
aexp ::= Nat | aexp + aexp | aexp - aexp | Var
bexp ::= aexp <= aexp | isZero aexp | bexp or bexp | not bexp
com ::= skip | while bexp do com end | if bexp then com else com end | Var := aexp | com ; com
```
