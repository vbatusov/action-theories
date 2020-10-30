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

    def symbols(self):
        yield self.symbol
        for arg in self.args:
            yield from arg.symbols()


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

    def terms(self):
        yield self
        for arg in self.args:
            yield from arg.terms()

    def tex(self):
        if self.symbol.infix: # binary, already checked
            return self.name().join([arg.tex() for arg in self.args])
        if self.arity == 0:
            return self.name
        return "{}({})".format(self.symbol.name, ", ".join([arg.tex() for arg in self.args]))


class Formula(object):
    """ Any FOL wff """
    # def __init__(self):
    #     pass
    #     # Nothing here

    def free_vars(self): # will this work?
        # all vars which are not in nonfree_vars
        yield from [v for v in self.vars() if v not in self.nonfree_vars()]
        # this works, which is pretty cool, since the methods invoked
        # here exist only in subclasses of Formula

    def is_sentence(self):
        return not [v for v in self.free_vars()]

    def describe(self):
        if self.is_sentence():
            print("I am a sentence {}".format(self.tex()))
        else:
            print("I am an open formula {}".format(self.tex()))
        print("  My variables: {}".format(", ".join([v.tex() for v in self.vars()])))
        print("  My non-free variables: {}".format(", ".join([v.tex() for v in self.nonfree_vars()])))
        print("  My free variables: {}".format(", ".join([v.tex() for v in self.free_vars()])))



class Atom(Formula, Struct):
    """ Atomic formula """
    def __init__(self, symbol, *args): # args must be Terms
        Formula.__init__(self)
        Struct.__init__(self, symbol, *args)

        if symbol.sort is not None:
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

    def terms(self):
        for arg in self.args:
            yield from arg.terms

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

    def symbols(self):
        yield from self.formula.symbols()

    def terms(self):
        yield from self.formula.terms()

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

    def symbols(self):
        for f in self.formulas:
            yield from f.symbols()

    def terms(self):
        for f in self.formulas:
            yield from f.terms()

    def tex(self, connective):
        joiner = " \\{} ".format(connective)
        return joiner.join([f.tex() for f in self.formulas])

# class To(Junction) # Strictly binary

# class Liff(Junction)  # Strictly binary

class And(Junction):
    def __init__(self, *formulas):
        Junction.__init__(self, *formulas)

    def tex(self):
        texes = ["({})".format(f.tex()) if isinstance(f, Or) else f.tex() for f in self.formulas]
        return " \\land ".join(texes)

class Or(Junction):
    def __init__(self, *formulas):
        Junction.__init__(self, *formulas)

    def tex(self):
        texes = ["({})".format(f.tex()) if isinstance(f, And) else f.tex() for f in self.formulas]
        return " \\lor ".join(texes)

class Implies(Junction):
    def __init__(self, *formulas):
        if len(formulas) != 2:
            raise Exception("Implication must be binary!")
        Junction.__init__(self, *formulas)

    def tex(self):
        tex1 = "({})".format(self.formulas[0].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[0].tex()
        tex2 = "({})".format(self.formulas[1].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[1].tex()
        return "{} \\to {}".join(tex1, tex2)

class Iff(Junction):
    def __init__(self, *formulas):
        if len(formulas) != 2:
            raise Exception("Bidirectional implication must be binary!")
        Junction.__init__(self, *formulas)

    def tex(self):
        tex1 = "({})".format(self.formulas[0].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[0].tex()
        tex2 = "({})".format(self.formulas[1].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[1].tex()
        return "{} \\liff {}".format(tex1, tex2)

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

    def symbols(self):
        yield self.var.symbol
        yield from self.formula.symbols()

    def terms(self):
        yield from self.formula.terms()

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

class RelSSA(Formula):
    """ Succcessor state axiom for a relational fluent
        Custom-form FOL formula for Basic Action Theories
    """
    def __init__(self, symbol):
        """ lhs = atom based on rel. fluent symbol with obj and sit variables as arguments
            rhs = disjunciton of effect and frame
            effect = disjunction of formulas 'a=namedaction(vars) and context_condition'

        """
        pass
        self.legal = False
        # Note to self: it will be better to hide construction complexity inside of this class
        # get as inputs only the necessary stuff and build the axiom incrementally
        # add quantifiers automatically, based on the fluent symbol
        # I.e., knowing fluent symbol already allows us to build the axiom using standard variables:
        # F(x1, x2, do(a,s)) \liff F(x1, x2, s)
        # Then, use add methods to add positive and negative effects

    def add_pos_effect(self, action, context):
        pass

    def add_neg_effect(self, action, context):
        pass

# Likewise, need to define FuncSSA and APA
# May leave APA for later, as it's not needed for regression
