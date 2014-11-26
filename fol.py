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

  def get_children(self):
    return self.children

  def set_children(self,children):
    self.children = children

  def push_negation(self):
    pass

  def negate(self):
    self.negated = not self.negated

class Function(Nested):
  def __init__(self, name, *children, negated=False):
    super().__init__(name, children)
    self.negated = negated

  def __eq__(self, f):
    return isinstance(f, Function) and f.name == self.name and f.children == self.children

class Variable(Atom):
  def __init__(self, name):
    self.name = name

  def __eq__(self, v):
    return isinstance(v, Variable) and v.name == self.name

  def __str__(self):
    return self.name

class Predicate(Nested):
  def __init__(self, name, *children, negated=False):
    super().__init__(name, children)
    self.negated = negated

  def __str__(self):
    if self.negated:
      return chr(172) + super().__str__()
    else:
      return super().__str__()

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
    # code point 8896 is the unicode for the and symbol
    separator = " " + chr(8896) + " "
    s = "{" + separator.join([str(x) for x in self.children]) + "}"
    if self.negated:
      s = chr(172) + s
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
    # code point 8897 is the unicode for the or symbol
    separator = " " + chr(8897) + " "
    s = "{" + separator.join([str(x) for x in self.children]) + "}"
    if self.negated:
      s = chr(172) + s
    return s

class Implication(Connective):
  def __init__(self, anticedent, consequent, negated = False):
    self.anticedent = anticedent
    self.consequent = consequent
    self.negated = negated

  def get_or(self):
    temp = deepcopy(self.anticedent)
    temp.negate()
    return Or([temp, deepcopy(self.consequent)], self.negated)

  def __str__(self):
    s = "[" + str(self.anticedent) + " ==> " + str(self.consequent) + "]"
    if self.negated:
      s = chr(172) + s
    return s

  def flip(self):
    temp = deepcopy(self.consequent)
    temp.negate()
    return And([deepcopy(self.anticedent),temp])

class Equivalence(Connective):
  def __init__(self, statement1, statement2, negated = False):
    self.statement1 = statement1
    self.statement2 = statement2
    self.negated = negated

  def get_implications(self):
    return And([Implication(self.statement1, self.statement2),
      Implication(self.statement2, self.statement1)],self.negated)

  def __str__(self):
    s = "[" + str(self.statement1) + " <=> " + str(self.statement2) + "]"
    if self.negated:
      s = chr(172) + s
    return s

  def flip(self):
    return Or([Implication(deepcopy(self.statement1), deepcopy(self.statement2, negated=True)),
            Implication(deepcopy(self.statement2), deepcopy(self.statement1, negated=True))])

class Quantifier():
  def negate(self):
    self.negated = not self.negated

  def push_negation(self):
    if self.negated:
      return self.flip()
    else:
      return self

class ForAll(Quantifier):
  def __init__(self, variable_name, statement, negated = False):
    self.variable_name = variable_name
    self.statement = statement
    self.negated = negated

  def flip(self):
    temp = deepcopy(self.statement)
    temp.negate()
    return ThereExists(self.variable_name,temp)

  def __str__(self):
    s = chr(8704) + self.variable_name + str(self.statement)
    if self.negated:
      s = chr(172) + s
    return s

class ThereExists(Quantifier):
  def __init__(self, variable_name, statement, negated = False):
    self.variable_name = variable_name
    self.statement = statement
    self.negated = negated

  def flip(self):
    temp = deepcopy(self.statement)
    temp.negate()
    return ForAll(self.variable_name,temp)

  def __str__(self):
    s = chr(8707) + self.variable_name + str(self.statement)
    if self.negated:
      s = chr(172) + s
    return s

def remove_equivalences(statement):
  if isinstance(statement, Predicate):
    pass
  elif isinstance(statement, And ) or isinstance(statement, Or):
    statement.children = [remove_equivalences(c) for c in statement.children]

  elif isinstance(statement, Implication):
    statement.anticedent = remove_equivalences(statement.anticedent)
    statement.consequent = remove_equivalences(statement.consequent)

  elif isinstance(statement, Equivalence):
    statement = statement.get_implications()

    return remove_equivalences(statement)

  elif isinstance(statement, Quantifier):
    statement.statement = remove_equivalences(statement.statement)
  return statement

def remove_implications(statement):
  if isinstance(statement, Predicate):
    pass
  elif isinstance(statement, And ) or isinstance(statement, Or):
    statement.children = [remove_implications(c) for c in statement.children]

  elif isinstance(statement, Implication):
    statement = remove_implications(statement.get_or())

  elif isinstance(statement, Quantifier):
    statement.statement = remove_implications(statement.statement)

  return statement

def push_nots_inwards(statement):
  if isinstance(statement, Predicate):
    pass
  elif isinstance(statement, And ) or isinstance(statement, Or):
    if statement.negated:
      statement = statement.push_negation()
    statement.children = [push_nots_inwards(c) for c in statement.children]
  elif isinstance(statement, Quantifier):
    statement = statement.push_negation()
    statement.statement = push_nots_inwards(statement.statement)
  return statement

def standardize_apart(statement, variable_name = None, change_variable = False, change = ""):
  if isinstance(statement, Variable):
    if statement.name == variable_name and change_variable:
      statement.name = statement.name + change
  elif isinstance(statement, Nested):
    temp = [None] * len(statement.get_children())
    for i in range(len(statement.get_children())):
      temp[i] = standardize_apart(statement.get_children()[i], variable_name, change_variable, change)
    statement.set_children(temp)
  elif isinstance(statement, And) or isinstance(statement, Or):
    for i in range(len(statement.children)):
      statement.children[i] = standardize_apart(statement.children[i],variable_name,True, change)
    for i in range(len(statement.children)):
      for j in range(i+1,len(statement.children)):
        for k in (x for x in get_variables(statement.children[i]) if x in get_variables(statement.children[j])):
          change = str(next(gen))
          statement.children[j] = standardize_apart(statement.children[j],k,True, change)
  elif isinstance(statement, Quantifier):
    var = statement.variable_name
    if var == variable_name:
      change = str(next(gen))
      statement.variable_name = var + change
      statement.statement = standardize_apart(statement.statement, var, True, change)
    else:
      statement.statement = standardize_apart(statement.statement, variable_name, change_variable, change)
      statement.statement = standardize_apart(statement.statement, var, False)
  return statement

def get_variables(statement):
  if isinstance(statement, Variable):
    yield statement
  elif isinstance(statement, Nested):
    for i in range(len(statement.get_children())):
      for x in get_variables(statement.get_children()[i]):
        yield x
  elif isinstance(statement, And) or isinstance(statement, Or):
    for i in range(len(statement.children)):
      for x in get_variables(statement.children[i]):
        yield x
  elif isinstance(statement, Quantifier):
    yield statement.variable_name
    for x in get_variables(statement.statement):
      yield x

def sequence_generator():
  x = 0
  while True:
    yield x
    x += 1

def cnf(statement):
  print(statement)
  print("\nremove equivalences")
  statement = remove_equivalences(statement)
  print(statement)
  print("\nremove implications")
  statement = remove_implications(statement)
  print(statement)
  print("\npush not inwards")
  statement = push_nots_inwards(statement)
  print(statement)
  print('\nStandardize Apart')
  statement = standardize_apart(statement)
  print(statement)

if __name__ == "__main__":
  global gen
  gen = sequence_generator()
  p1 = Predicate('P', Variable('x'))
  p2 = Predicate('Q', Variable('x'))
  p3 = Predicate('Q', Variable('y'))
  f1 = Predicate('R', Variable('y'), Variable('y'))
  expression = ForAll('x', Equivalence(p1, And([p2, ThereExists('y',And([p3,f1 ]) )]) ) )
  cnf(expression)

  # test expressions for standardize apart
  # expression = ForAll('x', ThereExists('y', ThereExists('y', Predicate('p',Variable('x')))))
  # expression = And([ForAll('x',Predicate('P', Variable('x'))), ThereExists('x',Predicate('P', Variable('x'))),ThereExists('x',Predicate('P', Variable('x')))])
  # expression = ForAll('x', And([ ThereExists('y', Predicate('p',Variable('y'))), ThereExists('y', Predicate('p',Variable('y')))]))
  # print(expression)
  # print('\n\n')
  # expression = remove_implications(expression)
  # print(standardize_apart(expression))
