from formula import *

def legal_name(n):
    #if not n.isalpha():
    #    raise Exception("Bad name '{}'".format(n))
    return n

class Theory:
    """ A vocabulary and a set of formulas over that vocabulary.
        Maintains a map of all mentions of each symbol.
        Handles the creation of legal formulas (wff).
        Can either add new formulas to itself,
        or just returns without adding, to be used for regression.

        Generic class, so allows arbitrary sorts
    """
    def __init__(self, name, sorts=[], subsets=[]):
        self.name = legal_name(name)
        # Let's agree to have just one arity and type per symbol name
        # There is literally no downside to this
        self.sorts = ["reals", "object", None] # Default sorts. None is for predicates
        for s in sorts: # Custom sorts
            self.add_sort(s)

        self.vocabulary = {} # Maps symbol_name to Symbol
        self.axioms = {"default" : set()} # Sets of Formula objects (no free variables)
        # It's a dict because we want to allow one to categorize axioms into subsets.
        for subset in subsets:
            self.axioms[subset] = set()
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

    def add_axiom(self, formula, force=False, where="default"): # force means force-add unknown symbols to vocab.
        """ Formula must be a sentence over the vocabulary """
        # Check if every symbol used in the formula
        # (including quantified variables, because they may not occur
        # anywhere as arguments) is in theory's vocabulary
        if not formula.is_sentence():
            raise Exception("An open formula cannot be an axiom!")
            # Future: automatically quantify free vars with \forall

        if formula in self.axioms[where]:
            raise Exception("Axiom already a part of theory!")

        for s in formula.symbols():
            if s not in self.vocabulary.values():
                if not force:
                    raise Exception("Symbol {} is not in {}'s vocabulary!".format(s.name, self.name))
                else:
                    print("Warning: forcing new symbol {} into vocabulary".format(s.name))
                    self.add_symbol(s)

        self.axioms[where].add(formula)



    def print_vocabulary(self):
        print("Vocabulary of theory '{}':".format(self.name))
        for s_n, s in self.vocabulary.items():
            print("  \t{}".format(str(s)))


class BasicActionTheory(Theory):
    """ Predetermined sorts and general syntactic form:
        \\Sigma, D_{ap}, D_{ss}, D_{una}, D_{S_0} """
    def __init__(self, name):
        Theory.__init__(self, name, sorts=["action", "situation"], subsets=["S_0", "ss", "ap"]) # una and \Sigma are standard
        # Here, add standard sitcalc symbols and terms to vocab.
        self.vocabulary = {}
        self.vocabulary["S_0"] = Term(Symbol("S_0", sort="situation"))
        self.vocabulary["do"] = Symbol("do", sort="situation", sorts=["action", "situation"])
        self.vocabulary["Poss"] = Symbol("Poss", sorts=["action", "situation"]),
        self.vocabulary["a"] = Term(Symbol("a", sort="action", is_var=True))
        self.vocabulary["s"] = Term(Symbol("s", sort="situation", is_var=True))
        self.vocabulary["Poss"] = Symbol("Poss", sorts=["action", "situation"])
        self.vocabulary["do(a,s)"] =Term(self.vocabulary["do"], self.vocabulary["a"], self.vocabulary["s"])


    def add_axiom(self, formula, force=False, where="default"):
        raise Exception("Don't do this. Use specialized methods.")

    #def uniform_in(self.)

    def add_init_axiom(self, formula, force=False):
        # check if it's a sentence uniform in S_0
        # need formula.terms() generator to get all situations to test
        pass

    def add_ap_axiom(self, formula, force=False):
        # Check if it's a proper Poss axiom
        pass

    def add_ss_axiom(self, formula, force=False):
        # Check if it's a proper ssa
        if (isinstance(formula, RelSSA) or isinstance(formula, FuncSSA)) and formula.finalized:
            self.axioms["ss"].add(formula)
        else:
            raise Exception("Not a proper SSA, cannot add to theory")

class HybridTheory(BasicActionTheory):
    """ Adds new axiom class: D_{sea} """
    def __init__(self, name):
        Theory.__init__(self, name)
