import pdb
from copy import deepcopy, copy

# Unicode code points for pretty printing of mathematical symbols
FORALL = chr(8704)
THEREEXISTS = chr(8707)
NOT = chr(172)
CONJUNCTION = chr(8896)
DISJUNCTION = chr(8897)

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
      return NOT + super().__str__()
    else:
      return super().__str__()

class Connective():
  def negate(self):
    self.negated = not self.negated

  def get_children(self):
    return self.children

  def set_children(self, children):
    self.children = children

  def push_negation(self):
    if self.negated:
      return self.flip()
    else:
      return self

class And(Connective):
  def __init__(self, *predicates, negated=False):
    self.children = predicates
    self.negated = negated

  def flip(self):
      temp = deepcopy(self.children)
      for x in temp:
        x.negate()
      return Or(*temp)

  def __str__(self):
    # code point 8896 is the unicode for the and symbol
    separator = " " + CONJUNCTION + " "
    s = "{" + separator.join([str(x) for x in self.children]) + "}"
    if self.negated:
      s = NOT + s
    return s

class Or(Connective):
  def __init__(self, *predicates, negated=False):
    self.children = predicates
    self.negated = negated

  def flip(self):
    temp = deepcopy(self.children)
    for x in temp:
      x.negate()
    return And(*temp)

  def __str__(self):
    # code point 8897 is the unicode for the or symbol
    separator = " " + DISJUNCTION + " "
    s = "{" + separator.join([str(x) for x in self.children]) + "}"
    if self.negated:
      s = NOT + s
    return s

class Implication(Connective):
  def __init__(self, anticedent, consequent, negated = False):
    self.anticedent = anticedent
    self.consequent = consequent
    self.negated = negated

  def get_or(self):
    self.anticedent.negate()
    return Or(self.anticedent, self.consequent, negated=self.negated)

  def __str__(self):
    s = "[" + str(self.anticedent) + " ==> " + str(self.consequent) + "]"
    if self.negated:
      s = NOT + s
    return s

  def get_children(self):
    return [self.anticedent, self.consequent]

  def set_children(self, children):
    self.anticedent, self.consequent = children

  def flip(self):
    temp = deepcopy(self.consequent)
    temp.negate()
    return And(deepcopy(self.anticedent),temp)

class Equivalence(Connective):
  def __init__(self, statement1, statement2, negated = False):
    self.statement1 = statement1
    self.statement2 = statement2
    self.negated = negated

  def get_implications(self):
    return And(Implication(deepcopy(self.statement1), deepcopy(self.statement2)),
      Implication(deepcopy(self.statement2), deepcopy(self.statement1)), negated=self.negated)

  def get_children(self):
    return [self.statement1, self.statement2]

  def set_children(self, children):
    self.statement1, self.statement2 = children

  def __str__(self):
    s = "[" + str(self.statement1) + " <=> " + str(self.statement2) + "]"
    if self.negated:
      s = NOT + s
    return s

  def flip(self):
    return Or(Implication(deepcopy(self.statement1), deepcopy(self.statement2), negated=True),
            Implication(deepcopy(self.statement2), deepcopy(self.statement1), negated=True))

class Quantifier():
  def negate(self):
    self.negated = not self.negated

  def get_children(self):
    return [self.statement]

  def set_children(self, children):
    self.statement = children[0]

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
    s = FORALL + self.variable_name + str(self.statement)
    if self.negated:
      s = NOT + s
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
    s = THEREEXISTS + self.variable_name + str(self.statement)
    if self.negated:
      s = NOT + s
    return s
