import pdb
from copy import deepcopy
import random

class Atom():
  pass

class Nested(Atom):
  def __init__(self, name, children=[]):
    self.children = children
    self.name = name

  def __str__(self):
    if len(self.children) > 0:
      return self.name + "(" + ", ".join(map(str, self.children)) + ")"
    else:
      return self.name

  def get_children(self):
    return self.children

  def set_children(self,children):
    self.children = children

class Function(Nested):
  def __init__(self, name, *children, negated=False):
    super().__init__(name, children)
  def __eq__(self, f):
    return isinstance(f, Function) and f.name == self.name and f.children == self.children

class Variable(Atom):
  def __init__(self, name, negated = False):
    self.name = name
    self.negated = negated

  def __eq__(self, v):
    return isinstance(v, Variable) and v.name == self.name

  def negate(self):
    self.negated = not self.negated

  def __str__(self):
    if self.negated:
      return " Not [ " + self.name + " ] "
    return self.name

class Predicate(Nested):
  def __init__(self, name, *children, negated=False):
    super().__init__(name, children)
    self.negated = negated

  def push_negation(self):
    pass

  def negate(self):
    self.negated = not self.negated

  def __str__(self):
    if self.negated:
      return "NOT[ " + super(Predicate,self).__str__() + " ]"
    else:
      return super(Predicate,self).__str__()

class Connective():
  def negate(self):
    self.negated = not self.negated

  def push_negation(self):
    if self.negated:
      return self.flip()
    else:
      return self

class And(Connective):
  def __init__(self, predicates=[], negated=False):
    self.children = predicates
    self.negated = negated

  def flip(self):
      temp = deepcopy(self.children)
      for x in temp:
        x.negate()
      return Or(temp)

  def __str__(self):
    s = " { "
    for x in self.children:
      s += str(x)
      s += " } . { "
    s = s[:-4]
    if self.negated:
      s = "Not [ " + s + " ]"
    return s

class Or(Connective):
  def __init__(self, predicates=[], negated=False):
    self.children = predicates
    self.negated = negated

  def flip(self):
    temp = deepcopy(self.children)
    for x in temp:
      x.negate()
    return And(temp)

  def __str__(self):
    s = " { "
    for x in self.children:
      s += str(x)
      s += " } | { "
    s = s[:-4]
    if self.negated:
      s = "Not [ " + s + " ]"
    return s

class Implication(Connective):
  def __init__(self, anticedent, consequent, negated = False):
    self.anticedent = anticedent
    self.consequent = consequent
    self.negated = negated

  def convert(self):
    temp = self.anticedent
    temp.negate()
    return Or([temp, self.consequent])

  def __str__(self):
    s = " [ " + str(self.anticedent) + " -> " + str(self.consequent) + " ] "
    if self.negated:
      s = "Not [ " + s + " ]"
    return s

  def flip(self):
    temp = self.consequent
    temp.negate()
    return And([self.anticedent,temp])

class Equivalence(Connective):
  def __init__(self, statement1, statement2, negated = False):
    self.statement1 = statement1
    self.statement2 = statement2
    self.negated = negated

  def convert(self):
    return And([Implication(self.statement1, self.statement2),
      Implication(self.statement2, self.statement1)])

  def __str__(self):
    s = " [ " + str(self.statement1) + " <-> " + str(self.statement2) + " ] "
    if self.negated:
      s = "Not [ " + s + " ]"
    return s

  def flip(self):
    temp1 = Implication(self.statement1, self.statement2)
    temp1.negate()
    temp2 = Implication(self.statement2, self.statement1)
    temp2.negate()
    return Or([temp1, temp2])

class Quantifier():
  def negate(self):
    self.negated = not self.negated

  def push_negation(self):
    if self.negated:
      return self.flip()
    else:
      return self

class ForAll(Quantifier):
  def __init__(self, variable, statement, negated = False):
    self.variable = variable
    self.statement = statement
    self.negated = negated

  def flip(self):
    temp = self.statement
    temp.negate()
    return ThereExists(self.variable,temp)

  def __str__(self):
    s = "FOR_ALL(" + str(self.variable) + ") {" + str(self.statement) + "}"
    if self.negated:
      s = "Not [ " + s + " ]"
    return s

class ThereExists(Quantifier):
  def __init__(self, variable, statement, negated = False):
    self.variable = variable
    self.statement = statement
    self.negated = negated

  def flip(self):
    temp = self.statement
    temp.negate()
    return ForAll(self.variable,temp)

  def __str__(self):
    s = "THERE_EXISTS(" + str(self.variable) + ") {" + str(self.statement) + "}"
    if self.negated:
      s = "Not [ " + s + " ]"
    return s

def remove_equivalences(statement):
  if isinstance(statement, Predicate):
    pass
  elif isinstance(statement, And ) or isinstance(statement, Or):
    for i in range(len(statement.children)):
      statement.children[i] = remove_equivalences(statement.children[i])
  elif isinstance(statement, Implication):
    statement.anticedent = remove_equivalences(statement.anticedent)
    statement.consequent = remove_equivalences(statement.consequent)
  elif isinstance(statement, Equivalence):
    statement = statement.convert()
    return remove_equivalences(statement)
  elif isinstance(statement, Quantifier):
    statement.statement = remove_equivalences(statement.statement)
  return statement

def remove_implications(statement):
  if isinstance(statement, Predicate):
    pass
  elif isinstance(statement, And ) or isinstance(statement, Or):
    for i in range(len(statement.children)):
      statement.children[i] = remove_implications(statement.children[i])
  elif isinstance(statement, Implication):
    statement = statement.convert()
    return remove_implications(statement)
  elif isinstance(statement, Quantifier):
    statement.statement = remove_implications(statement.statement)
  return statement

def push_nots_inwards(statement):
  if isinstance(statement, Predicate):
    pass
  elif isinstance(statement, And ) or isinstance(statement, Or):
    if statement.negated:
      statement = statement.push_negation()
      for i in range(len(statement.children)):
        statement.children[i] = push_nots_inwards(statement.children[i])
  elif isinstance(statement, Quantifier):
    statement = statement.push_negation()
    statement.statement = push_nots_inwards(statement.statement)
  return statement

def standardize_apart(statement, variable = None, change_variable = False, change = ""):
  if isinstance(statement, Variable):
    if statement.name == variable and change_variable:
      statement.name = statement.name + change
  elif isinstance(statement, Predicate) or isinstance(statement, Function):
    temp = [None] * len(statement.get_children())
    for i in range(len(statement.get_children())):
      temp[i] = standardize_apart(statement.get_children()[i],variable,change_variable, change)
    statement.set_children(temp)
  elif isinstance(statement, And ) or isinstance(statement, Or):
    for i in range(len(statement.children)):
      statement.children[i] = standardize_apart(statement.children[i],variable,True, change)
  elif isinstance(statement, ForAll) or isinstance(statement, ThereExists):
    var = statement.variable
    if var == variable or change_variable:
      change = str(random.randint(0,100))
      statement.variable = var + change
      statement.statement = standardize_apart(statement.statement, var, True, change)
    else:
      statement.statement = standardize_apart(statement.statement, var, False)
  return statement

def cnf(statement):
  print("remove equivalences")
  statement = remove_equivalences(statement)
  print(statement)
  print("\nremove implications")
  statement = remove_implications(statement)
  print(statement)
  print("\npush not inwards")
  statement = push_nots_inwards(statement)
  print(statement)
  print("\nstandardize apart")
  statement = standardize_apart(statement)
  print(statement)

if __name__ == "__main__":
  random.seed()
  temp = Predicate("P",Variable("x"))
  temp.negate()
  expression1 = ThereExists('x', ForAll('x', ThereExists('x', ForAll('x', Predicate("P",Variable("x")) ) ) ) )
  expression2 = And([ThereExists('x', ForAll('x', ThereExists('x', ForAll('x', Predicate("P",Variable("x")) ) ) ) ),expression1])
  cnf(expression1)
  cnf(expression2)