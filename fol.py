import pdb
from copy import deepcopy

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

class connectives():
  def negate(self):
    self.negated = not self.negated

  def push_negation(self):
    if self.negated:
      return self.flip()
    else:
      return self

class And(connectives):
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

class Or(connectives):
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

class Implication(connectives):
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

class Equivalence(connectives):
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
    remove_equivalences(statement.statement)
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
    remove_implications(statement.statement)
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

if __name__ == "__main__":
  e1 = And([Predicate("P", Function("f", Variable("x"))), Predicate("P",
        Function("g", Variable("x")))])
  e2 = Or([Predicate("P", Function("h", Variable("x"))), Predicate("i",
        Function("g", Variable("x")))])
  e3 = Implication(e1, e2)
  e4 = Equivalence(e1,e2)
  e5 = ThereExists(Variable("x"), And([Predicate("P", Function("f", Variable("x"))),
        Predicate("P", Function("g", Variable("x")))]))
  e6 = ForAll(Variable("x"), And([Predicate("P", Function("f", Variable("x"))),
        Predicate("P", Function("g", Variable("x")))]))
  print("Orignal Expression:")
  print("Expression 1: ", e1)
  print("Expression 2: ", e2)
  print("Expression 3: ", e3)
  print("Expression 4: ", e4)
  print("Expression 5: ", e5)
  print("Expression 6: ", e6)

  print("\n\nNegated Expressions")
  e1.negate()
  e2.negate()
  e3.negate()
  e4.negate()
  e5.negate()
  e6.negate()
  print("Expression 7: ", e1)
  print("Expression 8: ", e2)
  print("Expression 9: ", e3)
  print("Expression 10: ", e4)
  print("Expression 11: ", e5)
  print("Expression 12: ", e6)

  print("\n\nPushed Negation Expressions")
  e13 = e1.push_negation()
  e14 = e2.push_negation()
  e15 = e3.push_negation()
  e16 = e4.push_negation()
  e17 = e5.push_negation()
  e18 = e6.push_negation()
  print("Expression 13: ", e13)
  print("Expression 14: ", e14)
  print("Expression 15: ", e15)
  print("Expression 16: ", e16)
  print("Expression 17: ", e17)
  print("Expression 18: ", e18)

  print("\n\nRemoving Equivalences")
  test1 = Equivalence(Equivalence(Equivalence(Variable('x'), Variable('x')), Variable('x')), Variable('z'))
  test2 = Or([Equivalence(Variable('x'), Variable('y')),Variable('z')])
  print(test1)
  print(remove_equivalences(test1))
  print("\n")
  print(test2)
  print(remove_equivalences(test2))

  print("\n\nRemoving Implications")
  test3 = Implication(Implication(Variable('x'), Variable('y')), Variable('z'))
  test4 = Implication(Implication(Implication(Variable('x'), Variable('x')), Variable('x')), Variable('z'))
  print(test3)
  print(remove_implications(test3))
  print("\n")
  print(test4)
  print(remove_implications(test4))

  print("\n\nPush Not")
  test5 = And([And([Predicate("P", Function("f", Variable("x"))), Predicate("P",
        Function("g", Variable("x")))]), Predicate("P",Function("g", Variable("x")))])
  test6 = ForAll(Variable("x"), And([Predicate("P", Function("f", Variable("x"))),
        Predicate("P", Function("g", Variable("x")))]))
  test5.negate()
  test6.negate()
  print(test5)
  print(push_nots_inwards(test5))
  print("\n")
  print(test6)
  print(push_nots_inwards(test6))
