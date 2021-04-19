#! /usr/bin/env python3

import sys
from copy import copy, deepcopy
import random

# Literal
class Literal:
    def __init__(self, name, sign):
        self.name = name  # integer
        self.sign = sign  # boolean

    def __repr__(self):
        return ("-" if not self.sign else "") + self.name

    def __eq__(self, other):
        if type(other) != Literal:
            return False
        return self.name == other.name and self.sign == other.sign

    def __hash__(self):
      return hash((self.name, self.sign))

# Clause
class Clause:
    def __init__(self, id, literalSet):
        self.id = id
        self.literalSet = literalSet

    def __repr__(self):
        return f"{self.id}: {str(self.literalSet)}"

    def __eq__(self, other):
        if type(other) != Clause:
            return False
        return self.id == other.id


# Read and parse a cnf file, returning the variable set and clause set
def readInput(cnfFile):
    variableSet = []
    clauseSet = []
    nextCID = 0
    with open(cnfFile, "r") as f:
        for line in f.readlines():
            tokens = line.strip().split()
            if tokens and tokens[0] != "p" and tokens[0] != "c":
                literalSet = []
                for lit in tokens[:-1]:
                    sign = lit[0] != "-"
                    variable = lit.strip("-")

                    literalSet.append(Literal(variable, sign))
                    if variable not in variableSet:
                        variableSet.append(variable)

                clauseSet.append(Clause(nextCID, literalSet))
                nextCID += 1
    
    return variableSet, clauseSet

# Format literals into Forge code.
def formatLiterals(variableSet):
    ret = "Literal = " + " + ".join([ "L" + x for x in variableSet ])
    return ret

# Format clauses into Forge code.
def formatClause(clauseSet):
    ret = "Clause = " + " + ".join([ "C" + str(x.id) for x in clauseSet ])
    return ret

# Format one literal assignment into Forge code.
def formatOne(clauseId, literal):
    sign = "True" if literal.sign else "False"
    return "C" + str(clauseId) + "->L" + literal.name + "->" + sign + "0"

# Format all literals into Forge code.
def formatLitset(clauseSet):
    litsetList = []
    for c in clauseSet:
        for l in c.literalSet:
            litsetList.append((c.id, l))
    ret = "litset = " + " + ".join([ formatOne(x[0], x[1]) for x in litsetList ])
    return ret

# Run.
if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: ./generate.py <filename>")
        exit(0)
    
    inputFile = sys.argv[1]
    variableSet, clauseSet = readInput(inputFile)
    print(formatLiterals(variableSet))
    print(formatClause(clauseSet))
    print(formatLitset(clauseSet))
    