from fol import *

def remove_equivalences(statement):
  if isinstance(statement, Predicate):
    pass
  elif isinstance(statement, Equivalence):
    statement = remove_equivalences(statement.get_implications())
  elif isinstance(statement, Quantifier):
    statement.statement = remove_equivalences(statement.statement)
  elif hasattr(statement, "get_children"):
    statement.set_children([remove_equivalences(s) for s in statement.get_children()])
  return statement

def remove_implications(statement):
  if isinstance(statement, Predicate):
    pass
  elif isinstance(statement, Implication):
    statement = remove_implications(statement.get_or())
  elif isinstance(statement, Quantifier):
    statement.statement = remove_implications(statement.statement)
  elif hasattr(statement, "get_children"):
    statement.set_children([remove_implications(c) for c in statement.get_children()])
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

def get_new_variable(used_names):
  for i in range(1, 5):
    for char in range(ord("z"), ord("k"), -1):
      char = chr(char)*i
      if char not in used_names:
        return char

def get_new_constant(used_names):
  for i in range(1, 5):
    for char in range(ord("a"), ord("k")):
      char = chr(char)*i
      if char not in used_names:
        return char

def standardize_apart(statement, scope={}, used_names=[]):
  if isinstance(statement, Variable):
    if statement.name in scope:
      statement.name = scope[statement.name]
    else:
      raise Exception()
  elif isinstance(statement, Quantifier):
    if statement.variable_name not in used_names:
      scope[statement.variable_name] = statement.variable_name
      used_names.append(statement.variable_name)
    else:
      sub = get_new_variable(used_names)
      scope[statement.variable_name] = sub
      statement.variable_name = sub
      used_names.append(sub)
    statement.statement = standardize_apart(statement.statement, scope, used_names)
  elif hasattr(statement, "get_children"):
    statement.set_children([standardize_apart(s, scope, used_names) for s in statement.get_children()])
  return statement

def get_functions(statement):
  if isinstance(statement, Function):
    return [statement.name]
  if hasattr(statement, "get_children"):
    return [f for s in statement.get_children() for f in get_functions(s)]
  else:
    return []

def skolemize(statement, to_skolemize={}, quantified_variables=[], used_names=None):
  if used_names is None:
    used_names = get_functions(statement)
  if isinstance(statement, Variable):
    if statement.name in to_skolemize:
      name, variables = to_skolemize[statement.name]
      statement = Function(name, *[Variable(v) for v in variables])
  elif isinstance(statement, ThereExists):
    new_constant = get_new_constant(used_names)
    to_skolemize[statement.variable_name] = (new_constant, copy(quantified_variables))
    used_names.append(new_constant)
    statement = skolemize(statement.statement, to_skolemize, quantified_variables, used_names)
  elif isinstance(statement, ForAll):
    quantified_variables.append(statement.variable_name)
    statement.statement = skolemize(statement.statement, to_skolemize, quantified_variables, used_names)
  elif hasattr(statement, "get_children"):
    statement.set_children([skolemize(s, to_skolemize, quantified_variables, used_names) for s in statement.get_children()])
  return statement

def discard_forall(statement):
  if isinstance(statement, ForAll):
    statement = statement.statement
  if hasattr(statement, "get_children"):
    statement.set_children([discard_forall(s) for s in statement.get_children()])
  return statement

def vertical_merge(statement):
  if isinstance(statement, Connective):
    new_children = []
    for child in statement.get_children():
      vertical_merge(child)
      if isinstance(child, statement.__class__):
        new_children += child.get_children()
      else:
        new_children.append(child)
    statement.set_children(new_children)

def push_or(statement):
  if isinstance(statement, Or):
    children = []
    and_child = None
    for child in statement.get_children():
      child = push_or(child)
      if isinstance(child, And) and and_child is None:
        and_child = child
      else:
        children.append(child)
    if and_child is not None:
      statement = And(children=[Or(children=[c]+children) for c in and_child.get_children()])
  if hasattr(statement, "get_children"):
    statement.set_children([push_or(c) for c in statement.get_children()])
  return statement

def to_cnf(statement):
  vertical_merge(statement)
  statement = push_or(statement)
  vertical_merge(statement)
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
  print('\nSkolemize')
  statement = skolemize(statement)
  print(statement)
  print('\nRemoving For All quatifiers')
  statement = discard_forall(statement)
  print(statement)
  print('\nTo CNF')
  statement = to_cnf(statement)
  print(statement)

if __name__ == "__main__":
  p1 = Predicate('P', Variable('x'))
  p2 = Predicate('Q', Variable('x'))
  p3 = Predicate('Q', Variable('y'))
  f1 = Predicate('R', Variable('y'), Variable('x'))
  expression = ThereExists('x', Equivalence(p1, And(p2, ThereExists('y',And(p3,f1) )) ) )
  cnf(expression)

  e = Or(And(Variable('x'), Or(Variable('w'), Variable('v'))),
      And(Variable('y'), Or(Variable('z'), Variable('k'))))
  e = to_cnf(e)
  print(e)

  # test expressions for standardize apart
  # expression = ForAll('x', ThereExists('y', ThereExists('y', Predicate('p',Variable('x')))))
  # expression = And([ForAll('x',Predicate('P', Variable('x'))), ThereExists('x',Predicate('P', Variable('x'))),ThereExists('x',Predicate('P', Variable('x')))])
  # expression = ForAll('x', And([ ThereExists('y', Predicate('p',Variable('y'))), ThereExists('y', Predicate('p',Variable('y')))]))
  # print(expression)
  # print('\n\n')
  # expression = remove_implications(expression)
  # print(standardize_apart(expression))
