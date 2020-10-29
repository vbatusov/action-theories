class Struct:
    """ The syntactic structure underlying
        both Term and Atom. Needed for storing methods
        common to both and thus get rid of repetition.
        Contains:
            - underlying Symbol
            - actual Struct arguments, their number and sorts
              conforming to Symbol
        Does:
            - Test for bad arguments
            - Provide iterator for all Structs therein
        Does not contain:
            - Any semantic notions, i.e., whether variable or not
    """
    def __init__(self, symbol, *args):  # args are Structs
        if len(args) != symbol.arity:
            raise TypeError("Wrong number of arguments - {} instead of {}!".format(len(args), symbol.arity))

        for s_sort, arg in zip(symbol.sorts, args):
            if s_sort != arg.sort:
                raise Exception("Wrong argument sort. Expecting {}, got {}!".format(s_sort, arg.sort()))

        self.symbol = symbol
        self.args = list(args)
        # inherited from symbol for convenience
        self.sort = self.symbol.sort
        self.arity = self.symbol.arity
        self.name = self.symbol.name

    def __eq__(self, other):
        if self.symbol == other.symbol:
            # If same symbol, can safely assume arities match
            for arg1, arg2 in zip(self.args, other.args):
                if arg1 != arg2: # Recursively invoke comparison
                    return False
            return True
        return False

    def iter_structs(self): # All Atoms and Terms
        yield self
        for arg in self.args:
            for struct in arg.iter_structs():
                yield struct

    def iter_vars(self): # All Terms with is_var
        for struct in self.iter_structs():
            if struct.symbol.is_var:
                yield struct


class Term(Struct): #
    """ A term built using variables and function symbols
        For ease of use, construction should infer sorts from arguments
        Can construct term via args and sort, and infer term's symbol, if necessary
     """
    # Term(Symbol, Term, Term, ...)
    def __init__(self, symbol, *args):
        Struct.__init__(self, symbol, *args)
        self.is_var = symbol.is_var

    def __str__(self):
        return self.tex()

    def tex(self):
        if self.symbol.infix: # binary, already checked
            return self.name().join([arg.tex() for arg in self.args])
        if self.arity == 0:
            return self.name
        return "{}({})".format(self.symbol.name, ", ".join([arg.tex() for arg in self.args]))


class Formula(object):
    """ Any FOL wff """
    def __init__(self):
        pass
        # Nothing here

    def free_vars(self): # will this work?
        # all vars which are not in nonfree_vars
        yield from [v for v in self.vars() if v not in self.nonfree_vars()]

class Atom(Formula, Struct):
    """ Atomic formula """
    def __init__(self, symbol, *args): # args must be Terms
        Formula.__init__(self)
        Struct.__init__(self, symbol, *args)

        if symbol.type != "predicate":
            raise TypeError("Cannot make an atom out of {}".format(str(symbol)))

    # Having free_vars and non_free vars requires duplication of logic
    # Better define vars and nonfree_vars, and get free_vars by difference
    def vars(self): # generator
        # All variables in an atom are free
        for var in self.iter_vars():
            yield var

    def nonfree_vars(self): # generator
        return # It's an atom
        yield

    def tex(self):
        if len(self.args) > 0:
            return "{}({})".format(self.symbol.name, ", ".join([arg.tex() for arg in self.args]))
        return self.symbol.name

class Neg(Formula): # negation
    def __init__(self, formula):
        Formula.__init__(self)
        # No constraints. Any formula can be negated.
        self.formula = formula

    def vars(self): # generator
        # All variables in an atom are free
        yield from self.formula.vars()

    def nonfree_vars(self): # generator
        yield from self.formula.nonfree_vars()

    def tex(self):
        if isinstance(self.formula, Junction):
            return "\\neg ({})".format(self.formula.tex())
        else:
            return "\\neg {}".format(self.formula.tex())

class Junction(Formula):
    def __init__(self, *formulas): # a list of formulas in junction
        Formula.__init__(self)
        if len(formulas) < 2:
            raise Exception("A binary connective needs at least two formulas!")
        # No constraints. Any formula can be negated.
        self.formulas = list(formulas)

    def vars(self): # generator
        for f in self.formulas:
            yield from f.vars()

    def nonfree_vars(self): # generator
        for f in self.formulas:
            yield from f.nonfree_vars()

    def tex(self, connective):
        joiner = " \\{} ".format(connective)
        return joiner.join([f.tex() for f in self.formulas])

# class To(Junction) # Strictly binary

# class Liff(Junction)  # Strictly binary

class And(Junction):
    def __init__(self, *formulas):
        Junction.__init__(self, *formulas)

    def tex(self):
        #return Junction.tex(self, "land")

        # If one of the formulas is a disjunction, encase it brackets,
        # pass others as is. Then join.

        texes = ["({})".format(f.tex()) if isinstance(f, Or) else f.tex() for f in self.formulas]
        return " \\land ".join(texes)

class Or(Junction):
    def __init__(self, *formulas):
        Junction.__init__(self, *formulas)

    def tex(self):
        #return Junction.tex(self, "lor")

        texes = ["({})".format(f.tex()) if isinstance(f, And) else f.tex() for f in self.formulas]
        return " \\lor ".join(texes)

class Quantified(Formula):
    """ <quantifier> var (formula) """
    def __init__(self, var, formula):
        Formula.__init__(self)
        # var should be a Variable
        # formula should be a well-formed formula
        # formula cannot quantify over var (throw exc.)
        if not var.is_var:
            raise Exception("{} is not a variable, cannot quantify over it!".format(str(var)))
        if var in formula.nonfree_vars():
            raise Exception("Formula {} already quantifies over {}".format(formula.tex(), var.tex()))
        # This code is suspect, revise after testing all of the above
        elif var not in formula.vars():
            print("Warning: formula {} does not have free {} to quantify over!".format(formula.tex(), var.tex()))
        self.var = var
        self.formula = formula

    def vars(self): # generator
        yield from self.formula.vars()

    def nonfree_vars(self): # generator
        yield self.var
        yield from self.formula.nonfree_vars()

    def tex(self, quantifier):
        template = "\\{} {} {}"
        if isinstance(self.formula, Junction):
            template = "\\{} {}({})"
        return template.format(quantifier, self.var.tex(), self.formula.tex())

class Forall(Quantified):
    """ \\forall var (formula) """
    def __init__(self, var, formula):
        Quantified.__init__(self, var, formula)

    def tex(self):
        return Quantified.tex(self, "forall")

class Exists(Quantified):
    """ \\exists var (formula) """
    def __init__(self, var, formula):
        Quantified.__init__(self, var, formula)

    def tex(self):
        return Quantified.tex(self, "exists")
