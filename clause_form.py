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

def get_all_of_type(statement, klass):
  if isinstance(statement, klass):
    return [statement.name]
  elif hasattr(statement, "get_children"):
    return [f for s in statement.get_children() for f in get_all_of_type(s, klass)]
  elif hasattr(statement, "__iter__"):
    return [f for s in statement for f in get_all_of_type(s, klass)]
  else:
    return []

def skolemize(statement, to_skolemize={}, quantified_variables=[], used_names=None):
  if used_names is None:
    used_names = get_all_of_type(statement, Function)
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
  clause_form = []
  for d in statement.get_children():
    if isinstance(d, Predicate):
      clause_form.append(set([d]))
    else:
      clause_form.append(set(d.get_children()))
  return clause_form

def stringify_clause_form(clause_form):
  s = "{\n {"
  s +="},\n {".join([", ".join([s for s in map(str, x)]) for x in clause_form])
  s += "}\n}"
  return s

def change_clause_form_variable(clause, src_name, destination_name):
  if hasattr(clause, "__iter__"):
    clause = [change_clause_form_variable(c, src_name, destination_name)
        for c in clause]
  elif hasattr(clause, "get_children"):
    clause.set_children([change_clause_form_variable(c, src_name,
      destination_name) for c in clause.get_children()])
  else:
    if isinstance(clause, Variable) and clause.name == src_name:
      clause.name = destination_name
  return clause

def clause_form_standardize_apart(clause_form):
  standardized_clause_form = []
  used_names = set()
  for clause in clause_form:
    common_variables = \
        set(get_all_of_type(clause, Variable)).intersection(used_names)
    used_names.update(get_all_of_type(clause, Variable))
    for variable in common_variables:
      new_variable = get_new_variable(used_names)
      clause = change_clause_form_variable(clause, variable, new_variable)
      used_names.add(new_variable)
    standardized_clause_form.append(clause)
  return standardized_clause_form

def get_clause_form(statement, trace=False):
  print(statement)
  pp(trace, "\nremove equivalences")
  statement = remove_equivalences(statement)
  pp(trace, statement)
  pp(trace, "\nremove implications")
  statement = remove_implications(statement)
  pp(trace, statement)
  pp(trace, "\npush negation")
  statement = statement.push_negation()
  pp(trace, statement)
  pp(trace, '\nStandardize Apart')
  statement = standardize_apart(statement)
  pp(trace, statement)
  pp(trace, '\nSkolemize')
  statement = skolemize(statement)
  pp(trace, statement)
  pp(trace, '\nRemoving For All quatifiers')
  statement = discard_forall(statement)
  pp(trace, statement)
  pp(trace, '\nTo CNF')
  statement = to_cnf(statement)
  pp(trace, statement)
  pp(trace, '\nTo Clause Form')
  statement = to_clause_form(statement)
  pp(trace, stringify_clause_form(statement))
  pp(trace, '\nTo Clause Form Standardize Apart')
  statement = clause_form_standardize_apart(statement)
  print("Final clause form:")
  print(stringify_clause_form(statement))

if __name__ == "__main__":
  expression = \
    ForAll('x',
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
  get_clause_form(expression, True)

  p1 = Predicate('P', Variable('x'), negated = True)
  p2 = Predicate('Q', Variable('x'))
  p3 = ForAll('x', Implication(p2, p1))
  p4 = Predicate('P', Variable('x'))
  expression = ThereExists('x', And(children=[p4, p3]))
  get_clause_form(expression)
