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

  def __str__(self):
    if self.negated:
      return "NOT[ " + super(Function,self).__str__() + " ]"
    else:
      return super(Function,self).__str__()

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

  def get_or(self):
    temp = deepcopy(self.anticedent)
    temp.negate()
    return Or([temp, deepcopy(self.consequent)], self.negated)

  def __str__(self):
    s = " [ " + str(self.anticedent) + " -> " + str(self.consequent) + " ] "
    if self.negated:
      s = "Not [ " + s + " ]"
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
    s = " [ " + str(self.statement1) + " <-> " + str(self.statement2) + " ] "
    if self.negated:
      s = "Not [ " + s + " ]"
    return s

  def flip(self):
    return Or([Implication(deepcopy(self.statement1), deepcopy(self.statement2, True)),
            Implication(deepcopy(self.statement2), deepcopy(self.statement1, True))])

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
    s = "FOR_ALL(" + str(self.variable_name) + ") {" + str(self.statement) + "}"
    if self.negated:
      s = "Not [ " + s + " ]"
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
    s = "THERE_EXISTS(" + str(self.variable_name) + ") {" + str(self.statement) + "}"
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
    statement = statement.get_implications()
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
    statement = statement.get_or()
    remove_implications(statement)
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

def get_variables(statement, return_variable_name = False):
  if isinstance(statement, Variable):
    # changed this to return variable name to be used in change_variables
    if return_variable_name:
      yield statement.name
    else:
      yield statement
  elif isinstance(statement, Nested):
    for i in range(len(statement.get_children())):
      for x in get_variables(statement.get_children()[i], return_variable_name):
        yield x
  elif isinstance(statement, And) or isinstance(statement, Or):
    for i in range(len(statement.children)):
      for x in get_variables(statement.children[i], return_variable_name):
        yield x
  elif isinstance(statement, Quantifier):
    yield statement.variable_name
    for x in get_variables(statement.statement, return_variable_name):
      yield x

def sequence_generator():
  x = 0
  while True:
    yield x
    x += 1

def skolemize(statement, variable_name = ""):
  if isinstance(statement, Nested):
    if not variable_name == "":
      statement = change_variables(statement, variable_name)
  elif isinstance(statement, And) or isinstance(statement, Or):
    for i in range(len(statement.children)):
      statement.children[i] = skolemize(statement.children[i], variable_name)
  elif isinstance(statement, ForAll):
    var = statement.variable_name
    # if not variable_name == "":
    #   statement.statement = skolemize(statement.statement,variable_name)
    # else:
    statement.statement = skolemize(statement.statement,var)
  elif isinstance(statement, ThereExists):
    var = statement.variable_name
    statement = statement.statement
    if not variable_name == "":
      statement = skolemize(statement,variable_name)
    else:
      statement = skolemize(statement,var)
  return statement

# changes all variables to be function of the given src_variable
def change_variables(statement, src_variable_name, destination_variable_name = ""):
  variables = set(get_variables(statement, True)) - set([src_variable_name])
  temp = list(statement.get_children())[::]
  for x in variables:
    func = Function('f' + x, src_variable_name)
    for k in range(len(statement.get_children())):
      if statement.get_children()[k].name == x:
        temp[k] = func
  statement.set_children(temp)
  return statement


def discard_forall(statement):
  if isinstance(statement, Predicate):
    pass
  elif isinstance(statement, And ) or isinstance(statement, Or):
    for i in range(len(statement.children)):
      statement.children[i] = discard_forall(statement.children[i])
  elif isinstance(statement, ForAll):
      statement.statement = discard_forall(statement.statement)
  elif isinstance(statement, ThereExists):
    statement = statement.statement
    statement = discard_forall(statement)
  return statement

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
  print('\nSkolomize')
  statement = skolemize(statement)
  print(statement)

if __name__ == "__main__":
  global gen
  gen = sequence_generator()
  p1 = Predicate('P', Variable('x'))
  p2 = Predicate('Q', Variable('x'))
  p3 = Predicate('Q', Variable('y'))
  f1 = Predicate('R', Variable('y'), Variable('x'))
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

  # expression = Predicate('p', Variable('x'), Variable('y'), Variable('x'), Variable('z') )
  # expression = ThereExists('y', Predicate('p', Variable('x'), Variable('y'), Variable('x') ))
  # expression = ThereExists('w',ThereExists('z', ThereExists('y', Predicate('p', Variable('x'), Variable('y'), Variable('x') ))))
  # expression = ThereExists('x',ThereExists('y', Predicate('p', Variable('x'), Variable('y') )))
  # expression = ThereExists('x',And([ForAll('u', Predicate('G',Variable('u'))),ThereExists('y', ThereExists('z', Predicate('p', Variable('x'), Variable('y'), Variable('z') )))]))
  # expression = ThereExists('y', And([Predicate('p',Variable('x')) , Predicate('p',Variable('x'))]))
  # print(expression)
  # expression = skolemize(expression)
  # print(expression)

  # expression = Predicate('p', Variable('x'), Variable('y'), Variable('x'), Variable('z') )
  # print(expression)
  # expression = change_variables(expression, 'y')
  # print(expression)