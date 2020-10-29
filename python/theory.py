def legal_name(n):
    if not n.isalpha():
        raise Exception("Bad name '{}'".format(n))
    return n

class Theory:
    """ A vocabulary and a set of formulas over that vocabulary.
        Maintains a map of all mentions of each symbol.
        Handles the creation of legal formulas (wff).
        Can either add new formulas to itself,
        or just returns without adding, to be used for regression.

        Generic class, so allows arbitrary sorts
    """
    def __init__(self, name, sorts=[]):
        self.name = legal_name(name)
        # Let's agree to have just one arity and type per symbol name
        # There is literally no downside to this
        self.sorts = ["reals", "object"] # Default sorts
        for s in sorts: # Custom sorts
            self.add_sort(s)

        self.vocabulary = {} # Maps symbol_name to Symbol
        self.axioms = set() # A set of Formula objects (no free variables)
        self.occurs = {} # A map from vocabulary to sentences with occurrences

    def add_sort(self, new_sort):
        if not legal_name(new_sort) or new_sort in self.sorts:
            raise TypeError("Cannot add sort '{}'".format(new_sort))
        self.sorts.append(new_sort)

    def add_symbol(self, symbol):
        # Check if name is legal
        if not legal_name(symbol.name):
            raise ValueError("Illegal symbol name '{}'".format(symbol.name))

        # Check if sorts are legal
        if symbol.sort not in self.sorts:
            raise TypeError("Sort {} not part of theory".format(symbol.sort))
        for s in symbol.sorts:
            if s not in self.sorts:
                raise TypeError("Sort {} not part of theory".format(s))

        # Check if symbol already added
        if symbol.name in self.vocabulary:
            raise Exception("Symbol {} already in vocabulary".format(str(symbol)))

        # Add only if legit
        self.vocabulary[symbol.name] = symbol

    def add_axiom(self, formula):
        """ Formula must be a sentence over the vocabulary """
        #if formula.
        #self.fo
        pass

    def print_vocabulary(self):
        print("Vocabulary of theory '{}':".format(self.name))
        for s_n, s in self.vocabulary.items():
            print("  {} \t{}".format(s.type, str(s)))


class BasicActionTheory(Theory):
    """ Predetermined sorts and general syntactic form:
        \\Sigma, D_{ap}, D_{ss}, D_{una}, D_{S_0} """
    def __init__(self, name):
        Theory.__init__(self, name)

class HybridTheory(BasicActionTheory):
    """ Adds new axiom class: D_{sea} """
    def __init__(self, name):
        Theory.__init__(self, name)
