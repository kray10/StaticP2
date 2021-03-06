# Copyright (c) 2011, Jay Conrod.
# All rights reserved.

# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice, this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#     * Neither the name of Jay Conrod nor the
#       names of its contributors may be used to endorse or promote products
#       derived from this software without specific prior written permission.

# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL JAY CONROD BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

# Modified by Kevin Ray and Johnathan Bliss, March 2019
# Changes made for EECS 743
# Removed eval functions for all classes as they are not necessary for reaching.
# Added the label member variable and the getLabel function to the classes to
#   track the labeling.
# In conjunction with label variable, added the assignLabel function to each
#   class that is associated with the reaching definition.
# Added the genZ3 function to each class that is associated with the reaching
#   definition
# Added a new class defintion to encapsulate the skip command statement.
# Modified getVars function to return all variables on both sides of the assignment.

from .equality import *

class Statement(Equality):
    pass

class Aexp(Equality):
    pass

class Bexp(Equality):
    pass

class AssignStatement(Statement):
    def __init__(self, name, aexp):
        self.name = name
        self.aexp = aexp
        self.label = None

    def __repr__(self):
        return 'AssignStatement(%s, %s)' % (self.name, self.aexp)

    def getVars(self, env):
        env.add(self.name)
        self.aexp.getVars(env)

    def assignLabels(self, labels):
        current = 1
        while str(current) in labels:
            current += 1
        self.label = str(current)
        labels.add(self.label)

    def genZ3(self, list, prev):
        ent = "(assert (forall ((v!1 Var) (l!1 Lab))\n(= (En"
        ent += self.label + " v!1 l!1) (Ex"
        ent += prev + " v!1 l!1))))\n"
        list.append(ent)

        exit = "(assert (forall ((v!1 Var) (l!1 Lab))\n(ite (= v!1 "
        exit += self.name + ")\n(ite (= l!1 L"
        exit += self.label + ")\n(Ex"
        exit += self.label + " v!1 l!1)\n(not (Ex"
        exit += self.label + " v!1 l!1)))\n(= (Ex"
        exit += self.label + " v!1 l!1) (En"
        exit += self.label + " v!1 l!1)))))\n"
        list.append(exit)

    def getLabel(self):
        return self.label

class CompoundStatement(Statement):
    def __init__(self, first, second):
        self.first = first
        self.second = second

    def __repr__(self):
        return 'CompoundStatement(%s, %s)' % (self.first, self.second)

    def getVars(self, env):
        self.first.getVars(env)
        self.second.getVars(env)

    def assignLabels(self, labels):
        self.first.assignLabels(labels)
        self.second.assignLabels(labels)

    def genZ3(self, list, prev):
        self.first.genZ3(list, prev)
        self.second.genZ3(list, self.first.getLabel())

    def getLabel(self):
        return self.second.getLabel()


class IfStatement(Statement):
    def __init__(self, condition, true_stmt, false_stmt):
        self.condition = condition
        self.true_stmt = true_stmt
        self.false_stmt = false_stmt
        self.label = None

    def __repr__(self):
        return 'IfStatement(%s, %s, %s)' % (self.condition, self.true_stmt, self.false_stmt)

    def getVars(self, env):
        self.condition.getVars(env)
        self.true_stmt.getVars(env)
        self.false_stmt.getVars(env)

    def assignLabels(self, labels):
        current = 1
        while str(current) in labels:
            current += 1
        self.label = str(current)
        labels.add(self.label)
        self.true_stmt.assignLabels(labels)
        self.false_stmt.assignLabels(labels)

    def genZ3(self, list, prev):
        ent = "(assert (forall ((v!1 Var) (l!1 Lab))\n(= (En"
        ent += self.label + " v!1 l!1) (Ex"
        ent += prev + " v!1 l!1))))\n"
        list.append(ent)
        self.true_stmt.genZ3(list, self.label)
        self.false_stmt.genZ3(list, self.label)
        exit = "(assert (forall ((v!1 Var) (l!1 Lab))\n(= (Ex"
        exit += self.label + " v!1 l!1) (or (Ex"
        exit += self.true_stmt.getLabel() + " v!1 l!1) (Ex"
        exit += self.false_stmt.getLabel() + " v!1 l!1)))))\n"
        list.append(exit)

    def getLabel(self):
        return self.label


class WhileStatement(Statement):
    def __init__(self, condition, body):
        self.condition = condition
        self.body = body
        self.label = None

    def __repr__(self):
        return 'WhileStatement(%s, %s)' % (self.condition, self.body)

    def getVars(self, env):
        self.condition.getVars(env)
        self.body.getVars(env)

    def assignLabels(self, labels):
        current = 1
        while str(current) in labels:
            current += 1
        self.label = str(current)
        labels.add(self.label)
        self.body.assignLabels(labels)

    def getLabel(self):
        return self.label

    def genZ3(self, list, prev):
        ent = "(assert (forall ((v!1 Var) (l!1 Lab))\n(= (En"
        ent += self.label + " v!1 l!1) (or (Ex"
        ent += prev + " v!1 l!1) (Ex"
        ent += self.body.getLabel() + " v!1 l!1)))))\n"
        list.append(ent)
        exit = "(assert (forall ((v!1 Var) (l!1 Lab))\n(= (Ex"
        exit += self.label + " v!1 l!1) (En"
        exit += self.label + " v!1 l!1))))\n"
        list.append(exit)
        self.body.genZ3(list, self.label)


# added skip statement to class definition
class SkipStatement(Statement):
    def __init__(self):
        self.label = None

    def __repr__(self):
        return 'SkipStatement()'

    def getVars(self, env):
        pass

    def assignLabels(self, labels):
        current = 1
        while str(current) in labels:
            current += 1
        self.label = str(current)
        labels.add(self.label)

    def getLabel(self):
        return self.label

    def genZ3(self, list, prev=None):
        ent = "(assert (forall ((v!1 Var) (l!1 Lab))\n(= (En"
        ent += self.label + " v!1 l!1) (Ex"
        ent += prev + " v!1 l!1))))\n"
        list.append(ent)
        exit = "(assert (forall ((v!1 Var) (l!1 Lab))\n(= (Ex"
        exit += self.label + " v!1 l!1) (En"
        exit += self.label + " v!1 l!1))))\n"
        list.append(exit)


class IntAexp(Aexp):
    def __init__(self, i):
        self.i = i

    def __repr__(self):
        return 'IntAexp(%d)' % self.i

    def getVars(self, env):
        pass


class VarAexp(Aexp):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return 'VarAexp(%s)' % self.name

    def getVars(self, env):
        env.add(self.name)


class BinopAexp(Aexp):
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

    def __repr__(self):
        return 'BinopAexp(%s, %s, %s)' % (self.op, self.left, self.right)

    def getVars(self, env):
        self.left.getVars(env)
        self.right.getVars(env)

class RelopBexp(Bexp):
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

    def __repr__(self):
        return 'RelopBexp(%s, %s, %s)' % (self.op, self.left, self.right)

    def getVars(self, env):
        self.left.getVars(env)
        self.right.getVars(env)



class AndBexp(Bexp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __repr__(self):
        return 'AndBexp(%s, %s)' % (self.left, self.right)

    def getVars(self, env):
        self.left.getVars(env)
        self.right.getVars(env)


class OrBexp(Bexp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __repr__(self):
        return 'OrBexp(%s, %s)' % (self.left, self.right)

    def getVars(self, env):
        self.left.getVars(env)
        self.right.getVars(env)

class NotBexp(Bexp):
    def __init__(self, exp):
        self.exp = exp

    def __repr__(self):
        return 'NotBexp(%s)' % self.exp

    def getVars(self, env):
        self.exp.getVars(env)
