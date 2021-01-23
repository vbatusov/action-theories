import copy
from colorama import Fore, Back, Style
import random

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
    """ Must have situation as last arg. sort
        For now, let the sort be reals-only
    """
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
                raise Exception(f"Wrong argument sort. Expecting {s_sort}, got {arg.sort}! Argument in question is {arg}.")
            if not isinstance(arg, Struct):
                raise TypeError("Struct argument is not a Struct!!")

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

    def rename(self, name):
        self.name = name
        self.symbol.name = name

    # Deprecated
    # def iter_structs(self): # All Atoms and Terms
    #     yield self
    #     for arg in self.args:
    #         for struct in arg.iter_structs():
    #             yield struct

    # Deprecated
    # def iter_vars(self): # All Terms with is_var
    #     for struct in self.iter_structs():
    #         if struct.symbol.is_var:
    #             yield struct

    def symbols(self):
        yield self.symbol
        for arg in self.args:
            yield from arg.symbols()

    def replace_term(self, term, new_term):
        """ OK to put this here, because an atom can't occur as an argument
            so won't be replaced as if it were a term """
        # assume current term is not equal to 'term'
        #self.args = [new_term if term == arg else arg for arg in self.args]
        #print(f"STRUCT: replacing {term.tex()} by {new_term.tex()}")
        if not isinstance(term, Term) or not isinstance(new_term, Term):
            raise TypeError(f"One or both terms involved in substitution is not a Term!")
        if term.sort != new_term.sort:
            raise TypeError(f"Sorts of the terms don't match! Can't replace {term.sort} by {new_term.sort}")

        new_args = []
        for arg in self.args:
            if arg == term:
                new_args.append(new_term)
            else: # take care to avoid side effects when modifying arg
                new_arg = copy.deepcopy(arg)
                new_arg.replace_term(term, new_term)
                new_args.append(new_arg)
        self.args = new_args


class Term(Struct): #
    """ A term built using variables and function symbols
        For ease of use, construction should infer sorts from arguments
        Can construct term via args and sort, and infer term's symbol, if necessary
     """
    # Term(Symbol, Term, Term, ...)
    def __init__(self, symbol, *args):
        for arg in args:
            if not isinstance(arg, Term):
                raise TypeError(f"Argument {arg} is not a Term!")
        #if symbol.name == "=":
        #    print("***Constructing and equality atom***")
        Struct.__init__(self, symbol, *args)
        self.is_var = symbol.is_var

    def __str__(self):
        return self.tex()

    def terms(self, sort="any"):
        if sort == "any" or self.sort == sort:
            yield self
        for arg in self.args:
            yield from arg.terms(sort=sort)

    def vars(self, sort="any"):
        for t in self.terms(sort=sort):
            if t.is_var:
                yield t

    def tex(self):
        # colours
        # Background = variable
        # No background = not variable
        functor = self.symbol.name
        col = Style.BRIGHT
        if self.symbol.sort == "situation":
            col += Fore.GREEN
        elif self.symbol.sort == "action":
            col += Fore.YELLOW
        elif self.symbol.sort == "object":
            col += Fore.MAGENTA
        elif self.symbol.sort == "reals":
            col += Fore.BLUE
        elif self.symbol.sort == "time":
            col += Fore.CYAN
        else:
            pass

        if self.symbol.is_var: # variables are red; override
            col += Back.WHITE

        functor = col + functor + Style.RESET_ALL



        if self.symbol.infix: # binary, already checked
            return functor.join([arg.tex() for arg in self.args])
        if self.arity == 0:
            return functor
        return "{}({})".format(functor, ", ".join([arg.tex() for arg in self.args]))

    def __hash__(self):
        return f"Term {self.tex()}".__hash__()


class NumTerm(Term): # numerical term
    """ Arithmetical terms are of sort reals
        They cover numerical constants and all arithmetical constructs over them """
    pass

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
        yield from set([v for v in self.vars() if v not in self.nonfree_vars()])
        # this works, which is pretty cool, since the methods invoked
        # here exist only in subclasses of Formula

    def open(self):
        """ Returns whatever the current formula contains under the leading universal quantifiers """
        if not self.is_sentence():
            raise Exception("Suppressing quantifiers in an open formula makes no sense. How are you going to distinguish between free variables and the universally quantified ones?")
        if not isinstance(self, Forall):
            raise Exception("Not a universally-quantified sentence.")
        formula = self
        while isinstance(formula, Forall):
            formula = formula.formula  # Dig through quantifiers
        return formula

    def close(self):
        formula = self
        if self.is_sentence():
            pass
            #raise Exception("Can't quantify a sentence") -- no need to fail here
        else:
            for var in self.free_vars():
                formula = Forall(var, formula)
        return formula

    def nonfree_vars(self):
        yield from []

    def terms(self, sort="any"):
        yield from []

    def vars(self, sort="any"):
        """ This should, in principle, replace the clunky Struct.iter_vars() """
        for t in self.terms(sort=sort):
            if t.is_var:
                yield t

    def atoms(self):
        yield from []

    def replace_term(self, term, new_term):
        """ Covers the case where substitution is trivial """
        pass

    def apply_substitution(self, old=[], new=[]):
        """ Produce a new formula which is the result of simultaneously replacing every term in 'old' by
            the respective term in 'old'. The whole point of this method is to avoid collisions and
            recursive substitutions.
            'old' and 'new' must be lists of Term objects
            'old' must not contain duplicates, because substitution is a function
            'old' must be all variables (this is essentially unification) (may relax later)
            This method returns a new formula!
        """
        result = copy.deepcopy(self)

        if len(old) != len(new) or len(set(old)) != len(old):
            raise Exception("Substitution specified incorrectly")
        for v in old:
            if not v.is_var:
                raise Exception("Substitution's 'from' must be variables")
        for (o,n) in zip(old, new):
            if o.sort != n.sort:
                raise Exception("Sort mismatch in substitution")
        # find all terms (inc. nested) in 'new'
        #print(f"Source: {', '.join([o.tex() for o in old])}")
        vars_in_new = set(t for v in new for t in v.vars())
        #print(f"Vars in new:", "; ".join([t.tex() for t in vars_in_new]))
        # find which ones are also members of 'old' -> set of collisions
        vars_in_old = set(old)
        rhs_vars = set(result.vars())
        all_vars = vars_in_old.union(vars_in_new.union(rhs_vars))
        collisions = vars_in_old.intersection(vars_in_new)
        #print(f"All vars:", "; ".join([t.tex() for t in all_vars]))
        #print(f"Collisions:", "; ".join([t.tex() for t in collisions]))
        # for each collision,
        for c in collisions:
        #  - generate a fresh name (not in either terms_in_new or old)
            c_new = copy.deepcopy(c)
            while c_new in all_vars:
                #print("Finding name...")
                c_new.rename(c.name + str(random.randint(1,10000))) # a hack, so what
            #print(f"Renaming {c.tex()} to {c_new.tex()}")
        #  - rename variable in 'result'
            result.replace_term(c, c_new)
        #  - rename source variable in rule accordingly
            old = [c_new if v == c else v for v in old]
        #print(f"RHS copy ready: {result.tex()}")
        #print(f"Source: {', '.join([o.tex() for o in old])}")
        # apply the substitutions without fear of messing up
        for (src, tgt) in zip(old, new):
            result.replace_term(src, tgt)

        return result

    def tex(self):
        return ""

    def is_sentence(self):
        return not [v for v in self.free_vars()]

    # def occurs_standalone(self, term):
    #     """ True if term occurs alone as an argument of an atom """
    #     for sigma in self.terms(sort="situation"):
    #         skip = True # skip if sigma is a sub-situation and not a stand-alone argument of an atom
    #         for atom in w.atoms():
    #             if sigma in atom.args:
    #                 skip = False
    #         if skip:
    #             continue
    #
    #         s = sigma


    def uniform_in(self, term):
        """ True iff, in self, every term of sort term.sort is term. """
        for t in self.terms(sort=term.sort):
            if term != t:
                print(f"Formula {self.tex()} is not uniform in {term.tex()} because it contains term {t.tex()}")
                return False
        return True

    def describe(self):
        if self.is_sentence():
            print("I am a sentence {}".format(self.tex()))
        else:
            print("I am an open formula {}".format(self.tex()))
        #print("  My variables (in order of appearance): {}".format(", ".join([v.tex() for v in self.vars()])))
        #print("  My non-free variables: {}".format(", ".join([v.tex() for v in self.nonfree_vars()])))
        free = ", ".join([v.tex() for v in self.free_vars()])
        nonfree = ", ".join([v.tex() for v in self.nonfree_vars()])
        (free, nonfree) = tuple(["none" if x == "" else x for x in (free, nonfree)])
        print("  Free variables: {}, non-free: {}".format(free, nonfree))

class Tautology(Formula):
    def tex(self):
        return "\\top"

class Contradiction(Formula):
    def tex(self):
        return "\\bot"

class Atom(Formula, Struct):
    """ Atomic formula """
    def __init__(self, symbol, *args): # args must be Terms
        if symbol.sort is not None:
            raise TypeError("Cannot make an atom out of {}".format(str(symbol)))
        for arg in args:
            if not isinstance(arg, Term):
                raise TypeError("Atom's arguments must be Terms!")

        Formula.__init__(self)
        Struct.__init__(self, symbol, *args)

    # Having free_vars and non_free vars requires duplication of logic
    # Better define vars and nonfree_vars, and get free_vars by difference
    # def vars(self): # generator
    #     # All variables in an atom are free
    #     yield from self.iter_vars()
    # THis is now handled by Formula's vars which relies on self.terms, which works really well.

    def nonfree_vars(self): # generator
        return # It's an atom
        yield

    def terms(self, sort="any"):
        for arg in self.args:
            yield from arg.terms(sort=sort)

    def atoms(self):
        yield self

    def replace_term(self, term, new_term):
        """ Use Struct's, and not Formula's, because Atom inherits from both"""
        Struct.replace_term(self, term, new_term)

    def tex(self):
        functor = Style.BRIGHT + Fore.WHITE + self.symbol.name + Style.RESET_ALL

        if len(self.args) > 0:
            return "{}({})".format(functor, ", ".join([arg.tex() for arg in self.args]))
        return self.symbol.name

class EqAtom(Atom):
    """ Might have to exclude the = symbol from all theories' vocabularies!
        Might have to look over all conditions that depend on isinstance(_, Atom)!

        Better idea: construct equality atoms in a factory belonging to THEORY.
        Because the treatment of equality may be theory-specific. *TODO*
        Actions have UNA; situations should not be equated at all...
        This class should be theory-agnostic, but it currently isn't
    """
    def __init__(self, *args):
        if len(args) != 2:
            raise TypeError(f"Equality must have two arguments, {len(args)} given.")
        if args[0].sort != args[1].sort:
            raise TypeError(f"Cannot equate terms of distinct sorts! {args[0].sort} vs. {args[1].sort}")
        if args[0].sort == "situation":
            raise Exception("Equality between situations is prohibited.")

        symbol = Symbol("=", sorts=[args[0].sort]*2) # Might have to exclude this from theory's vocabulary
        Atom.__init__(self, symbol, *args)

    def tex(self):
        return f"{self.args[0].tex()} \\eq {self.args[1].tex()}"

class Neg(Formula): # negation
    def __init__(self, formula):
        Formula.__init__(self)
        # No constraints. Any formula can be negated.
        self.formula = formula

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        f_under_neg = self.formula.simplified()
        if isinstance(f_under_neg, Contradiction):
            return Tautology()
        elif isinstance(f_under_neg, Tautology):
            return Contradiction()
        elif isinstance(f_under_neg, Neg):
            return f_under_neg.formula
        else:
            return Neg(f_under_neg)

    def vars(self, sort="any"): # generator
        # All variables in an atom are free
        yield from self.formula.vars(sort=sort)

    def nonfree_vars(self): # generator
        yield from self.formula.nonfree_vars()

    def symbols(self):
        yield from self.formula.symbols()

    def terms(self, sort="any"):
        yield from self.formula.terms(sort=sort)

    def atoms(self):
        yield from self.formula.atoms()

    def replace_term(self, term, new_term):
        #print(f"Negation: replacing {term.tex()} by {new_term.tex()}")
        self.formula.replace_term(term, new_term)

    def tex(self):
        if isinstance(self.formula, Junction) or isinstance(self.formula, EqAtom):
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

    def vars(self, sort="any"): # generator
        for f in self.formulas:
            yield from f.vars(sort=sort)

    def nonfree_vars(self): # generator
        for f in self.formulas:
            yield from f.nonfree_vars()

    def symbols(self):
        for f in self.formulas:
            yield from f.symbols()

    def terms(self, sort="any"):
        for f in self.formulas:
            yield from f.terms(sort)

    def atoms(self):
        for f in self.formulas:
            yield from f.atoms()

    def replace_term(self, term, new_term):
        #print(f"Junction: replacing {term.tex()} by {new_term.tex()}")
        for f in self.formulas:
            f.replace_term(term, new_term)

    def tex(self, connective):
        joiner = " \\{} ".format(connective)
        return joiner.join([f.tex() for f in self.formulas])


class And(Junction):
    def __new__(cls, *formulas, **kwargs):
        if len(formulas) == 0:
            print("Constructing And(Junction) from an empty set of formulas!!", formulas)
            #raise Exception("Let's take a look at the stack")
            return Tautology()
        elif len(formulas) == 1:
            return formulas[0]
        else:
            return super().__new__(cls) #, *formulas, **kwargs)

    def __init__(self, *formulas):
        Junction.__init__(self, *formulas)

    def __deepcopy__(self, memo):
        cp_f = copy.deepcopy(self.formulas, memo)
        return And(*cp_f)

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

    def __deepcopy__(self, memo):
        cp_f = copy.deepcopy(self.formulas, memo)
        return Or(*cp_f)

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

    def vars(self, sort="any"): # generator
        yield from self.formula.vars(sort=sort)

    def nonfree_vars(self): # generator
        yield self.var
        yield from self.formula.nonfree_vars()

    def symbols(self):
        yield self.var.symbol
        yield from self.formula.symbols()

    def terms(self, sort="any"):
        yield from self.formula.terms(sort=sort)

    def atoms(self):
        yield from self.formula.atoms()

    def replace_term(self, term, new_term):
        self.formula.replace_term(term, new_term)

    def tex(self, quantifier):
        template = "\\{} {} {}"
        if isinstance(self.formula, Junction) or isinstance(self.formula, EqAtom):
            template = "\\{} {} ({})"
        return template.format(quantifier, self.var.tex(), self.formula.tex())

class Forall(Quantified):
    """ \\forall var (formula) """
    def __init__(self, var, formula):
        Quantified.__init__(self, var, formula)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self
            Don't bother simplifying quantifiers for now """
        f_simplified = self.formula.simplified()
        if isinstance(f_simplified, Contradiction) or isinstance(f_simplified, Tautology):
            return f_simplified
        else:
            return Forall(copy.deepcopy(self.var), f_simplified)

    def tex(self):
        return Quantified.tex(self, "forall")

class Exists(Quantified):
    """ \\exists var (formula) """
    def __init__(self, var, formula):
        Quantified.__init__(self, var, formula)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self
            Don't bother simplifying quantifiers for now """
        f_simplified = self.formula.simplified()
        if isinstance(f_simplified, Contradiction) or isinstance(f_simplified, Tautology):
            return f_simplified
        else:
            return Exists(copy.deepcopy(self.var), f_simplified)

    def tex(self):
        return Quantified.tex(self, "exists")


class Theory:
    """ A vocabulary and a set of formulas over that vocabulary.
        Maintains a map of all mentions of each symbol.
        Handles the creation of legal formulas (wff).
        Can either add new formulas to itself,
        or just returns without adding, to be used for regression.

        Generic class, so allows arbitrary sorts
    """
    def __init__(self, name, sorts=[], subsets=[]):
        self.name = name
        # Let's agree to have just one arity and type per symbol name
        # There is literally no downside to this
        self.sorts = ["reals", "object", None] # Default sorts. None is for predicates
        for s in sorts: # Custom sorts
            self.add_sort(s)

        self.vocabulary = {} # Maps symbol_name to Symbol
        #self.vocabulary["="] = Symbol("=", sort="situation")
        # add arithmetics here?
        self.vocabulary["+"] = Symbol("+", sort="reals", sorts=["reals", "reals"], infix=True)
        self.vocabulary["-"] = Symbol("-", sort="reals", sorts=["reals", "reals"], infix=True)
        self.vocabulary["*"] = Symbol("*", sort="reals", sorts=["reals", "reals"], infix=True)
        self.vocabulary["/"] = Symbol("/", sort="reals", sorts=["reals", "reals"], infix=True)
        self.vocabulary["^"] = Symbol("^", sort="reals", sorts=["reals", "reals"], infix=True)

        self.axioms = {"default" : set()} # Sets of Formula objects (no free variables)
        # It's a dict because we want to allow one to categorize axioms into subsets.
        for subset in subsets:
            self.axioms[subset] = set()
        self.occurs = {} # A map from vocabulary to sentences with occurrences

    def add_sort(self, new_sort):
        if new_sort in self.sorts:
            raise TypeError("Cannot add sort '{}'".format(new_sort))
        self.sorts.append(new_sort)

    def add_symbol(self, symbol):
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
