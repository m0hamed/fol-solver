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

  def negate(self):
    self.negated = not self.negated

  def __str__(self):
    if self.negated:
      return "NOT[ " + super(Predicate,self).__str__() + " ]"
    else:
      return super(Predicate,self).__str__()


class And():
  def __init__(self, predicates=[]):
    self.children = predicates

  def negate(self):
    temp = deepcopy(self.children)
    for x in temp:
      # pdb.set_trace()
      x.negate()
    return Or(temp)

  def __str__(self):
    s = " { "
    for x in self.children:
      s += x.__str__()
      s += " } . { "
    s = s[:-4]
    return s

class Or():
  def __init__(self, predicates=[]):
    self.children = predicates

  def negate(self):
    temp = deepcopy(self.children)
    for x in temp:
      x.negate()
    return And(temp)

  def __str__(self):
    s = " { "
    for x in self.children:
      s += x.__str__()
      s += " } | { "
    s = s[:-4]
    return s

class Quantifier():
  def push_negation(self):
    if self.negated:
      return self.flip()
    else:
      return self

class ForAll(Quantifier):
  def __init__(self, variable, statement):
    self.variable = variable
    self.statement = statement

  def negate(self):
    return ThereExists(self.variable,self.statement.negate())

  def __str__(self):
    s = "FOR_ALL(" + self.variable.__str__() + ") {" + self.statement.__str__() + "}"
    return s

class ThereExists(Quantifier):
  def __init__(self, variable, statement):
    self.variable = variable
    self.statement = statement

  def negate(self):
    return ForAll(self.variable,self.statement.negate())

  def __str__(self):
    s = "THERE_EXISTS(" + self.variable.__str__() + ") {" + self.statement.__str__() + "}"
    return s

class Implication():
  def __init__(self, anticedent, consequent):
    self.anticedent = anticedent
    self.consequent = consequent

  def get_not_or_form(self):
    return Or([self.anticedent.negate, self.consequent])

  def __str__(self):
    s = self.anticedent.__str__() + " -> " + self.consequent.__str__()
    return s

  def negate(self):
    # pdb.set_trace()
    return And([self.anticedent,self.consequent.negate()])

class Equivalence():
  def __init__(self, statement1, statement2):
    self.statement1 = statement1
    self.statement2 = statement2

  def get_implication_form(self):
    return And([Implication(self.statement1, self.statement2),
      Implication(self.statement2, self.statement1)])

  def __str__(self):
    s = self.statement1.__str__() + " <-> " + self.statement2.__str__()
    return s

  def negate(self):
    return Or([Implication(self.statement1, self.statement2).negate(),
      Implication(self.statement2, self.statement1).negate()])

class Substitution:
  def __init__(self, variable, replacement):
    self.variable = variable
    self.replacement = replacement

  def __str__(self):
    return str(self.replacement) + "/" + str(self.variable)

def unify(formula1, formula2, mgu=[], trace=False):
  pp(trace, "Unifying expression:", formula1, "with expression:", formula2)
  if mgu is False:
    return False
  if formula1 == formula2:
    return mgu

  if isinstance(formula1, Nested) and isinstance(formula2, Nested):
    if type(formula1) != type(formula2) or formula1.name != formula2.name \
        or len(formula1.children) != len(formula2.children):
      return false
    else:
      for a,b in zip(formula1.children, formula2.children):
        mgu = unify(a, b, mgu, trace)
      return mgu

  if isinstance(formula1, Variable):
    return unify_variable(formula1, formula2, mgu, trace)
  if isinstance(formula2, Variable):
    return unify_variable(formula2, formula1, mgu, trace)

def substitute(mu, expression):
  for s in (x for x in mu if occurs_in(x.variable, expression)):
    if isinstance(expression, Variable):
      expression = s.replacement
    else:
      expression.children = [substitute(mu, e) for e in expression.children]
  return expression

def occurs_in(variable, expression):
  if expression == variable:
    return True
  if not isinstance(expression, Nested):
    return False
  return any([occurs_in(variable, e) for e in expression.children])

def unify_variable(variable, expression, mgu, trace):
  pp(trace, "Unifying variable:", variable, "with expression:", expression)
  for s in (s for s in mgu if s.variable == variable):
    return unify(s.replacement, expression, mgu, trace)
  t = substitute(mgu, expression)
  if occurs_in(variable, t):
    return False
  else:
    s = Substitution(variable, t)
    pp(trace, "MGU now is: ", ", ".join(map(str, mgu+[s])))
    return mgu+[s]

def pp(trace, *args):
  if trace:
    print(*args)

if __name__ == "__main__":
  e1 = Predicate("P", Function("f", Variable("u")), Variable("v"), Variable("v"))
  e2 = Predicate("P", Variable("x"), Function("g", Variable("x")), Function("g", Function("f", Function("a"))))
  mgu = unify(e1, e2, trace=True)
  print("Expression 1: ", e1)
  print("Expression 2: ", e2)
  if mgu is False:
    print("Not unifiable")
  else:
    print("MGU: ", ", ".join(map(str, mgu)))

  e1 = Predicate("P", Variable("a"), Variable("y"), Function("f", Variable("y")))
  e2 = Predicate("P", Variable("z"), Variable("z"), Variable("u"))
  mgu = unify(e1, e2)
  print("Expression 1: ", e1)
  print("Expression 2: ", e2)
  if mgu is False:
    print("Not unifiable")
  else:
    print("MGU: ", ", ".join(map(str, mgu)))

  e1 = Function("f", Variable("x"), Function("g", Variable("x")), Variable("x"))
  e2 = Function("f", Function("g", Variable("u")), Function("g", Function("g", Function("z"))), Variable("z"))
  mgu = unify(e1, e2)
  print("Expression 1: ", e1)
  print("Expression 2: ", e2)
  if mgu is False:
    print("Not unifiable")
  else:
    print("MGU: ", ", ".join(map(str, mgu)))

  print("\n\n\n\nStart of conjunctive normal form")

  e1 = And([Predicate("P", Function("f", Variable("x"))), Predicate("P",
        Function("g", Variable("x")))])
  e2 = Or([Predicate("P", Function("f", Variable("x"))), Predicate("P",
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

  e7 = e1.negate()
  e8 = e2.negate()
  e9 = e3.negate()
  e10 = e4.negate()
  e11 = e5.negate()
  e12 = e6.negate()
  print("Expression 7: ", e7)
  print("Expression 8: ", e8)
  print("Expression 9: ", e9)
  print("Expression 10: ", e10)
  print("Expression 11: ", e11)
  print("Expression 12: ", e12)
