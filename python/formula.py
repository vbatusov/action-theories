class Symbol:
    """ A symbol is always a part of a theory.
        Consists of a name, sort, number and sort of arguments,
        infix - for representation only
        is_var - flags a variable symbol (Note: SOL allows function variables)
    """
    def __init__(self, name, sorts=[], sort=None, infix=False, is_var=False):
        # If no return sort, assume it's a predicate
        # Let the parent theory check for legal sorts
        if sort is None:
            self.type = "predicate"
        else:
            if is_var: # No predicate variables, don't care
                self.type = "variable"
            else:
                self.type = "function" # includes constants

        if sort is None and is_var:
            raise Exception("A variable must have a sort")
        if infix and len(sorts) != 2:
            raise Exception("An infix symbol must be binary, and this one is {}-ary".format(len(sorts)))

        self.name = name
        self.sorts = sorts
        self.arity = len(sorts)
        self.sort = sort
        self.is_var = is_var
        self.infix = infix

    def __str__(self):
        strargs = ""
        if self.arity > 0:
            strargs = "({})".format(", ".join(["<{}>".format(s) for s in self.sorts]))
        retsort = ""
        if self.type != "predicate":
            retsort = " : <{}>".format(self.sort)
        return "{}{}{} - {}".format(self.name, strargs, retsort, self.type)

    def __eq__(self, other):
        if self.name == other.name and self.sorts == other.sorts and self.sort == other.sort and self.is_var == other.is_var and self.infix == other.infix:
            return True
        return False


class RelFluentSymbol(Symbol):
    """ Must have situation as last arg. sort"""
    def __init__(self, name, sorts=[]): # sorts don't include sit term at the end
        if "situation" in sorts:
            raise Exception("Cannot have a second situation term in a relational fluent")
        Symbol.__init__(self, name, sorts=sorts+["situation"])
        self.type = "relational fluent"

class FuncFluentSymbol(Symbol):
    """ Must have situation as last arg. sort"""
    def __init__(self, name, sorts=[], sort="reals"): # sorts don't include sit term at the end
        if "situation" in sorts:
            raise Exception("Cannot have a second situation term in a relational fluent")
        Symbol.__init__(self, name, sorts=sorts+["situation"], sort=sort)
        self.type = "functional fluent"

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
    def __init__(self):
        pass
        # Nothing here

    def simplified(self):
        """ Catch-all for formulas that don't have their own simplification method """
        return self

    def free_vars(self): # will this work?
        # all vars which are not in nonfree_vars
        yield from [v for v in self.vars() if v not in self.nonfree_vars()]
        # this works, which is pretty cool, since the methods invoked
        # here exist only in subclasses of Formula

    def vars(self):
        yield from []

    def nonfree_vars(self):
        yield from []

    def terms(self):
        yield from []

    def tex(self):
        return ""

    def is_sentence(self):
        return not [v for v in self.free_vars()]

    def describe(self):
        if self.is_sentence():
            print("I am a sentence {}".format(self.tex()))
        else:
            print("I am an open formula {}".format(self.tex()))
        print("  My variables (in order of appearance): {}".format(", ".join([v.tex() for v in self.vars()])))
        print("  My non-free variables: {}".format(", ".join([v.tex() for v in self.nonfree_vars()])))
        print("  My free variables: {}".format(", ".join([v.tex() for v in self.free_vars()])))

class Tautology(Formula):
    def tex(self):
        return "\\top"

class Contradiction(Formula):
    def tex(self):
        return "\\bot"

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

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        tmp = self.formula.simplified()
        if isinstance(tmp, Contradiction):
            return Tautology()
        elif isinstance(tmp, Tautology):
            return Contradiction()
        elif isinstance(tmp, Neg):
            return tmp.formula
        else:
            return self

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
        #if len(formulas) < 2:
        #    raise Exception("A binary connective needs at least two formulas!")
        # Let's relax this a bit --- allow empty junctions, handle depending on child class

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


class And(Junction):
    def __new__(cls, *formulas, **kwargs):
        if len(formulas) == 0:
            return Tautology()
        elif len(formulas) == 1:
            return formulas[0]
        else:
            return super().__new__(cls) #, *formulas, **kwargs)

    def __init__(self, *formulas):
        Junction.__init__(self, *formulas)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        new_formulas = []
        for f in self.formulas:
            tmp = f.simplified()
            if isinstance(tmp, Contradiction):
                return tmp
            elif isinstance(tmp, Tautology):
                pass
            else:
                new_formulas.append(tmp)
        return And(*new_formulas)

    def tex(self):
        texes = ["({})".format(f.tex()) if isinstance(f, Or) else f.tex() for f in self.formulas]
        return " \\land ".join(texes)

class Or(Junction):
    def __new__(cls, *formulas, **kwargs):
        if len(formulas) == 0:
            return Contradiction()
        elif len(formulas) == 1:
            return formulas[0]
        else:
            return super().__new__(cls)

    def __init__(self, *formulas):
        Junction.__init__(self, *formulas)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        new_formulas = []
        for f in self.formulas:
            tmp = f.simplified()
            if isinstance(tmp, Contradiction):
                pass
            elif isinstance(tmp, Tautology):
                return tmp
            else:
                new_formulas.append(tmp)
        return Or(*new_formulas)

    def tex(self):
        texes = ["({})".format(f.tex()) if isinstance(f, And) else f.tex() for f in self.formulas]
        return " \\lor ".join(texes)

class Implies(Junction):
    def __init__(self, *formulas):
        if len(formulas) != 2:
            raise Exception("Implication must be binary!")
        Junction.__init__(self, *formulas)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        premise = self.formulas[0].simplified()
        conclusion = self.formulas[1].simplified()
        if isinstance(premise, Tautology):
            return conclusion
        elif isinstance(premise, Contradiction):
            return Tautology()
        elif isinstance(conclusion, Tautology):
            return conclusion
        elif isinstance(conclusion, Contradiction):
            return Neg(premise).simplified()
        else:
            return Implies(premise, conclusion)


    def tex(self):
        tex1 = "({})".format(self.formulas[0].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[0].tex()
        tex2 = "({})".format(self.formulas[1].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[1].tex()
        return "{} \\to {}".join(tex1, tex2)

class Iff(Junction):
    def __init__(self, *formulas):
        if len(formulas) != 2:
            raise Exception("Bidirectional implication must be binary!")
        Junction.__init__(self, *formulas)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        left = self.formulas[0].simplified()
        right = self.formulas[1].simplified()
        if isinstance(left, Tautology):
            return right
        elif isinstance(left, Contradiction):
            return Neg(right).simplified()
        elif isinstance(right, Tautology):
            return left
        elif isinstance(right, Contradiction):
            return Neg(left).simplified()
        else:
            return Iff(left, right)

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
            template = "\\{} {} ({})"
        return template.format(quantifier, self.var.tex(), self.formula.tex())

class Forall(Quantified):
    """ \\forall var (formula) """
    def __init__(self, var, formula):
        Quantified.__init__(self, var, formula)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self
            Don't bother simplifying quantifiers for now """
        return Forall(self.var, self.formula.simplified())

    def tex(self):
        return Quantified.tex(self, "forall")

class Exists(Quantified):
    """ \\exists var (formula) """
    def __init__(self, var, formula):
        Quantified.__init__(self, var, formula)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self
            Don't bother simplifying quantifiers for now """
        return Exists(self.var, self.formula.simplified())

    def tex(self):
        return Quantified.tex(self, "exists")

class RelSSA(Formula):
    """ Successor state axiom for a relational fluent
        Custom-form FOL formula for Basic Action Theories
        Constructor only takes a relational fluent symbol and terms for variables
        The RHS is constructed sequentially by adding positive and negative effects
    """
    def __init__(self, symbol, obj_vars=[], voc={}):
        """ Classic Reiter's SSA
            F(\\bar{x}, do(a,s)) \liff [disj. of pos. effects] \lor F(\bar{x}, s)
              \land \neg [disj. of neg. effects]
            obj_vars are the \\bar{x}
            voc is the vocabulary containing terms 'do(a,s)', 'a', 's'
        """
        # Must maintain the pieces and the total formula in sync!
        if not isinstance(symbol, RelFluentSymbol):
            raise Exception("A relational SSA must be about a relational fluent")

        for v in obj_vars:
            if v.sort != "object":
                raise TypeError("Fluent object arguments must be of sort object")
        # Create universally quantified variables
        lhs_atom_args = obj_vars + [voc['do(a,s)']]
        rhs_atom_args = obj_vars + [voc['s']]

        self.univ_vars = obj_vars + [voc['a'], voc['s']]
        self.lhs = Atom(symbol, *lhs_atom_args)
        self.frame_atom = Atom(symbol, *rhs_atom_args)
        self.pos_effects = []
        self.neg_effects = []
        self.formula = None # this is just to indicate where the formula can be found
        self.build_formula() # reconcile bits into one formula

        # Note to self: it will be better to hide construction complexity inside of this class
        # get as inputs only the necessary stuff and build the axiom incrementally
        # add quantifiers automatically, based on the fluent symbol
        # I.e., knowing fluent symbol already allows us to build the axiom using standard variables:
        # F(x1, x2, do(a,s)) \liff F(x1, x2, s)
        # Then, use add methods to add positive and negative effects

    def simplified(self):
        raise Exception("Not supposed to do this on a SSA")

    def build_formula(self):
        p_eff = Or(*self.pos_effects)
        n_eff = Or(*self.neg_effects)
        frame = And(self.frame_atom, Neg(n_eff))
        iff = Iff(self.lhs, Or(p_eff, frame))

        quantified = iff
        for var in reversed(self.univ_vars):
            quantified = Forall(var, quantified)

        self.formula = quantified.simplified()

        if not self.formula.is_sentence():
            raise Exception("Resulting SSA is not a sentence. Perhaps an extra var in effects?")

    def add_pos_effect(self, action, context):
        """ action: fully instantiated action term with variables among obj_vars (for now) --- update later
            context: arbitrary formula uniform in s with free variables among obj_vars
            (a=action_name(\bar{x}) \land \Phi(\bar{x},s))
        """

        pass
        self.build_formula()

    def add_neg_effect(self, action, context):
        pass
        self.build_formula()

    def describe(self):
        self.formula.describe()

    def tex(self):
        return self.formula.tex()


# Likewise, need to define FuncSSA and APA
# May leave APA for later, as it's not needed for regression
