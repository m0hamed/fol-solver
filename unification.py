from fol import Predicate, Function, Variable, pp

# this represents a substitution with the variable name and the replacement
class Substitution:
  def __init__(self, variable, replacement):
    self.variable = variable
    self.replacement = replacement

  def __str__(self):
    return str(self.replacement) + "/" + str(self.variable)

# unifies two FOL expressions
def unify(formula1, formula2, mgu=[], trace=False):
  pp(trace, "Unifying expression:", formula1, "with expression:", formula2)
  if mgu is False:
    return False
  if formula1 == formula2:
    return mgu

  if hasattr(formula1, 'get_children') and hasattr(formula2, 'get_children'):
    if type(formula1) != type(formula2) or formula1.name != formula2.name \
        or len(formula1.get_children()) != len(formula2.get_children()):
      return false
    else:
      for a,b in zip(formula1.get_children(), formula2.get_children()):
        mgu = unify(a, b, mgu, trace)
      return mgu

  if isinstance(formula1, Variable):
    return unify_variable(formula1, formula2, mgu, trace)
  if isinstance(formula2, Variable):
    return unify_variable(formula2, formula1, mgu, trace)

# substitutes into an expression by a list of substitutions
def substitute(mu, expression):
  for s in (x for x in mu if occurs_in(x.variable, expression)):
    if isinstance(expression, Variable):
      expression = s.replacement
    else:
      expression.set_children([substitute(mu, e) for e in
          expression.get_children()])
  return expression

# checks if a variable occurs in an expression
def occurs_in(variable, expression):
  if expression == variable:
    return True
  elif hasattr(expression, 'get_children'):
    return any([occurs_in(variable, e) for e in expression.get_children()])
  else:
    return False

# tries to unify a variable with an expression given a list of prior substitutions
def unify_variable(variable, expression, mgu, trace):
  pp(trace, "Unifying variable:", variable, "with expression:", expression)
  for s in (s for s in mgu if s.variable == variable):
    return unify(s.replacement, expression, mgu, trace)
  t = substitute(mgu, expression)
  if occurs_in(variable, t):
    return False
  else:
    s = Substitution(variable, t)
    # for each substitution in the mgu substitute in the relacement expression
    # by the new substitution
    mgu = [Substitution(e.variable, substitute([s], e.replacement)) for e in mgu]
    pp(trace, "MGU now is: ", ", ".join(map(str, mgu+[s])))
    return mgu+[s]

# test cases
if __name__ == "__main__":
  e1 = Predicate("P", Function("f", Variable("u")), Variable("v"), Variable("v"))
  e2 = Predicate("P", Variable("x"), Function("g", Variable("x")), Function("g", Function("f", Function("a"))))
  print("Expression 1: ", e1)
  print("Expression 2: ", e2)
  print()
  mgu = unify(e1, e2, trace=True)
  print()
  if mgu is False:
    print("Not unifiable")
  else:
    print("MGU: ", ", ".join(map(str, mgu)))
  print()

  e1 = Predicate("P", Variable("a"), Variable("y"), Function("f", Variable("y")))
  e2 = Predicate("P", Variable("z"), Variable("z"), Variable("u"))
  print("Expression 1: ", e1)
  print("Expression 2: ", e2)
  mgu = unify(e1, e2)
  if mgu is False:
    print("Not unifiable")
  else:
    print("MGU: ", ", ".join(map(str, mgu)))
  print()

  e1 = Function("f", Variable("x"), Function("g", Variable("x")), Variable("x"))
  e2 = Function("f", Function("g", Variable("u")), Function("g", Function("g", Variable("z"))), Variable("z"))
  print("Expression 1: ", e1)
  print("Expression 2: ", e2)
  mgu = unify(e1, e2)
  if mgu is False:
    print("Not unifiable")
  else:
    print("MGU: ", ", ".join(map(str, mgu)))
  print()
