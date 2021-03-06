from fol import Predicate, Function, Variable, Nested, Atom

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
