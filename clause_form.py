from fol import *

def remove_equivalences(statement):
  if isinstance(statement, Nested):
    pass
  elif isinstance(statement, Equivalence):
    statement = remove_equivalences(statement.get_implications())
  elif isinstance(statement, Quantifier):
    statement.statement = remove_equivalences(statement.statement)
  elif hasattr(statement, "get_children"):
    statement.set_children([remove_equivalences(s) for s in statement.get_children()])
  return statement

def remove_implications(statement):
  if isinstance(statement, Nested):
    pass
  elif isinstance(statement, Implication):
    statement = remove_implications(statement.get_or())
  elif isinstance(statement, Quantifier):
    statement.statement = remove_implications(statement.statement)
  elif hasattr(statement, "get_children"):
    statement.set_children([remove_implications(c) for c in statement.get_children()])
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
    statement.name = scope[statement.name]
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
        new_children.append(deepcopy(child))
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

def to_clause_form(statement):
  s = set()
  for j in statement.get_children():
    temp = set()
    if not isinstance(j, Nested):
      for i in j.get_children():
        temp.add(i)
    else:
      temp.add(j)
    temp = frozenset(temp)
    s.add(temp)
  return s

def print_clause_form(statement):
  s = "{\n"
  for i in statement:
    s += " { "
    for j in i:
      s += str(j) + ", "
    s = s[:-2] + " },\n"
  s += "}"
  print(s)

def get_variables(statement):
  return  set(i.name for j in statement for i in j.get_children())

def change_clause_form_variable(statement, src_name, destination_name):
  for j in statement:
    for i in j.get_children():
      if i.name == src_name:
        i.name = destination_name
  return statement

def clause_form_standardize_apart(clause_form):
  standardized_clause_form = set()
  clause_form = list(clause_form)
  standardized_clause_form.add(frozenset(clause_form[0]))
  used_names = get_variables(clause_form[0])
  for i in range(1,len(clause_form)):
    temp = list(clause_form[i])
    common_variables = get_variables(clause_form[i]).intersection(used_names)
    used_names.update(get_variables(clause_form[i]))
    if not common_variables == list():
      for j in common_variables:
        new_variable = get_new_variable(used_names)
        change_clause_form_variable(temp, j, new_variable)
        used_names.add(new_variable)
    standardized_clause_form.add(frozenset(temp))
  return standardized_clause_form

def cnf(statement):
  print(statement)
  print("\nremove equivalences")
  statement = remove_equivalences(statement)
  print(statement)
  print("\nremove implications")
  statement = remove_implications(statement)
  print(statement)
  print("\npush negation")
  statement = statement.push_negation()
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
  print('\nTo Clause Form')
  statement = to_clause_form(statement)
  print_clause_form(statement)
  print('\nTo Clause Form Standardize Apart')
  statement = clause_form_standardize_apart(statement)
  print_clause_form(statement)

if __name__ == "__main__":
  expression = \
    ThereExists('x',
      Equivalence(
        Predicate('P', Variable('x')),
        And(
          Predicate('Q', Variable('x')),
          ThereExists('y',
            And(
              Predicate('Q', Variable('y')),
              Predicate('R', Variable('y'), Variable('x'))
            )
          )
        )
      )
    )
  cnf(expression)

  p1 = Predicate('P', Variable('x'), negated = True)
  p2 = Predicate('Q', Variable('x'))
  p3 = ForAll('x', Implication(p2, p1))
  p4 = Predicate('P', Variable('x'))
  expression = ThereExists('x', And(children=[p4, p3]))
  cnf(expression)
