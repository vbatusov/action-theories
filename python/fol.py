import copy
from colorama import Fore, Back, Style


# import random

class Symbol:
    """ A symbol is always a part of a theory.
        Consists of a name, sort, number and sort of arguments,
        infix - for representation only
        is_var - flags a variable symbol (Note: SOL allows function variables)
        unique_name - a flag to indicate that symbol is to be treated like a standard name (i.e., there is an implicit unique name axiom for it over its sort. This needs some further thinking. Let's say only constants and action functions can have unique names.)
    """

    def __init__(self, name, sorts=(), sort=None, infix=False, is_var=False, unique_name=False):
        # If no return sort, assume it's a predicate
        # Let the parent theory check for legal sorts
        if sort is None:
            self.type = "predicate"
        else:
            if is_var:  # No predicate variables, don't care
                self.type = "variable"
            else:
                self.type = "function"  # includes constants

        if sort is None and is_var:
            raise Exception("A variable must have a sort")
        if infix and len(sorts) != 2:
            raise Exception("An infix symbol must be binary, and this one is {}-ary".format(len(sorts)))
        if is_var and unique_name:
            raise Exception("Can't have a variable symbol with a unique name axiom!")
        self.name = name
        self.sorts = sorts
        self.arity = len(sorts)
        self.sort = sort
        self.is_var = is_var
        self.infix = infix
        self.unique_name = unique_name

    def __str__(self):
        strargs = ""
        if self.arity > 0:
            strargs = "({})".format(", ".join(["<{}>".format(s) for s in self.sorts]))
        retsort = ""
        if self.type != "predicate":
            retsort = " : <{}>".format(self.sort)
        return "{}{}{} - {}".format(self.name, strargs, retsort, self.type)

    def __eq__(self, other):
        if self.name == other.name and self.sorts == other.sorts and self.sort == other.sort and self.is_var == other.is_var and self.infix == other.infix and self.unique_name == other.unique_name:
            return True
        return False

    def __hash__(self):
        return f"Symbol named {self.name} of sort {self.sort} and argument sorts {[str(s) for s in self.sorts]} and is_var={self.is_var}".__hash__()


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
                raise Exception(
                    f"Wrong argument sort. Expecting {s_sort}, got {arg.sort}! Argument in question is {arg}.")
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
                if arg1 != arg2:  # Recursively invoke comparison
                    return False
            return True
        return False

    def is_atomic(self):
        return len(self.args) == 0

    def rename(self, name):
        self.name = name
        self.symbol.name = name

    def symbols(self):
        yield self.symbol
        for arg in self.args:
            yield from arg.symbols()

    def replace_term(self, term, new_term):
        """ OK to put this here, because an atom can't occur as an argument
            so won't be replaced as if it were a term """
        # assume current term is not equal to 'term'
        # self.args = [new_term if term == arg else arg for arg in self.args]
        # print(f"STRUCT: replacing {term.tex()} by {new_term.tex()}")
        if not isinstance(term, Term) or not isinstance(new_term, Term):
            raise TypeError(f"One or both terms involved in substitution is not a Term!")
        if term.sort != new_term.sort:
            raise TypeError(f"Sorts of the terms don't match! Can't replace {term.sort} by {new_term.sort}")

        new_args = []
        for arg in self.args:
            if arg == term:
                new_args.append(new_term)
            else:  # take care to avoid side effects when modifying arg
                new_arg = copy.deepcopy(arg)
                new_arg.replace_term(term, new_term)
                new_args.append(new_arg)
        self.args = new_args


class Term(Struct):  #
    """ A term built using variables and function symbols
        For ease of use, construction should infer sorts from arguments
        Can construct term via args and sort, and infer term's symbol, if necessary
     """

    # Term(Symbol, Term, Term, ...)
    def __init__(self, symbol, *args):
        for arg in args:
            if not isinstance(arg, Term):
                raise TypeError(f"Argument {arg} is not a Term!")
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

        if self.symbol.is_var:  # variables are red; override
            col += Back.WHITE

        functor = col + functor + Style.RESET_ALL

        if self.symbol.infix:  # binary, already checked
            return functor.join([arg.tex() for arg in self.args])
        if self.arity == 0:
            return functor
        return "{}({})".format(functor, ", ".join([arg.tex() for arg in self.args]))

    def __hash__(self):
        return f"Term {self.tex()}".__hash__()


class NumTerm(Term):  # numerical term
    """ Arithmetical terms are of sort reals
        They cover numerical constants and all arithmetical constructs over them """
    pass


class Formula(object):
    """ Any FOL wff """

    def __init__(self):
        pass
        # Nothing here

    def __eq__(self, other):
        return False  # Catch-all

    def __str__(self):
        return self.tex()

    def flatten(self, varsrc):
        """ Default case. All formulas that CAN be flattened must implement their own way. """
        return copy.deepcopy(self)

    def simplified(self):
        """ Catch-all for formulas that don't have their own simplification method """
        return copy.deepcopy(self)

    def simplified_stable(self):
        """ Simplified as many times as it takes to arrive at a stable formula """
        j = 0
        r = self.simplified()
        while j < 1000:
            r_new = r.simplified()
            if r.tex() == r_new.tex():
                return r
            j += 1
            r = r_new
        raise Exception(f"Simplified formula not stable after {j} iterations!")

    def free_vars(self):  # will this work?
        # all vars which are not in nonfree_vars
        yield from set([v for v in self.vars() if v not in self.nonfree_vars()])
        # this works, which is pretty cool, since the methods invoked
        # here exist only in subclasses of Formula

    def open(self):
        """ Returns whatever the current formula contains under the leading universal quantifiers """
        if not self.is_sentence():
            raise Exception(
                "Suppressing quantifiers in an open formula makes no sense. How are you going to distinguish between free variables and the universally quantified ones?")
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
            # raise Exception("Can't quantify a sentence") -- no need to fail here
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

    def apply_substitution(self, old=(), new=()):
        """ Produce a new formula which is the result of simultaneously replacing every term in 'old' by
            the respective term in 'old'. The whole point of this method is to avoid collisions and
            recursive substitutions.
            'old' and 'new' must be lists of Term objects
            'old' must not contain duplicates, because substitution is a function
            This method returns a new formula!
            Idea:
              - find all collisions between members of 'old' and terms (inc.nested) of 'new'.
              - for each such collision, rename the corresponding 'old' member to a ... TODO

        """
        # print(f"Subsitution:")
        # for o, n in zip(old, new):
        #     print(f"  {o} -> {n}")

        result = copy.deepcopy(self)

        if len(old) != len(new) or len(set(old)) != len(old):
            raise Exception("Substitution specified incorrectly")
        # for v in old:
        #    if not v.is_var:
        #        raise Exception("Substitution's 'from' must be variables")
        for (o, n) in zip(old, new):
            if o.sort != n.sort:
                raise Exception("Sort mismatch in substitution")

        vars_in_new = set(t for v in new for t in v.vars())
        vars_in_old = set(old)
        rhs_vars = set(result.vars())
        all_vars = vars_in_old.union(vars_in_new.union(rhs_vars))
        collisions = vars_in_old.intersection(vars_in_new)
        # for each collision,
        for c in collisions:
            #  - generate a fresh name (not in either terms_in_new or old)
            c_new = copy.deepcopy(c)
            i = 1
            while c_new in all_vars:
                # print("Finding name...")
                c_new.rename(f"{c.name}_{{i}}")
                i += 1
            #  - rename variable in 'result'
            result.replace_term(c, c_new)
            #  - rename source variable in rule accordingly
            old = [c_new if v == c else v for v in old]
        # apply the substitutions without fear of messing up
        for (src, tgt) in zip(old, new):
            result.replace_term(src, tgt)

        return result

    def tex(self):
        return ""

    def is_sentence(self):
        return not [v for v in self.free_vars()]

    def uniform_in(self, term):
        """ True iff, in self, every term of sort term.sort is term. """
        for t in self.terms(sort=term.sort):
            if term != t:
                return False
        return True

    def describe(self):
        if self.is_sentence():
            print("I am a sentence {}".format(self.tex()))
        else:
            print("I am an open formula {}".format(self.tex()))

        free = ", ".join([v.tex() for v in self.free_vars()])
        nonfree = ", ".join([v.tex() for v in self.nonfree_vars()])
        (free, nonfree) = tuple(["none" if x == "" else x for x in (free, nonfree)])
        print("  Free variables: {}, non-free: {}".format(free, nonfree))


class Tautology(Formula):
    def tex(self):
        return "\\top"

    def eval(self, semantics):
        return True  # Tautology is always true no matter what semantics is used


class Contradiction(Formula):
    def tex(self):
        return "\\bot"

    def eval(self, semantics):
        return False


class Atom(Formula, Struct):
    """ Atomic formula """

    def __init__(self, symbol, *args):  # args must be Terms
        if symbol.sort is not None:
            raise TypeError("Cannot make an atom out of {}".format(str(symbol)))
        for arg in args:
            if not isinstance(arg, Term):
                raise TypeError("Atom's arguments must be Terms!")

        Formula.__init__(self)
        Struct.__init__(self, symbol, *args)

    def __eq__(self, other):
        return isinstance(other, Atom) and ((self.symbol, self.args) == (other.symbol, other.args))

    def flatten(self, varsrc):
        """ Returns an equivalent, but flattened version of self.
            By flatten I mean no complex functional terms as arguments of either functions or fluents.
            Needed to convert functions to predicates for Prolog.
        """
        # print(f"Flattening Atom {self.tex()}")
        new_atom = copy.deepcopy(self)
        i = -1

        for j in range(0, len(new_atom.args)):
            if not new_atom.args[j].is_atomic():
                i = j
                break

        if i >= 0:
            new_var = varsrc.new("z", new_atom.args[i].sort)
            old_term = new_atom.args[i]
            new_atom.args[i] = new_var
            existential = Exists(new_var, And(new_atom, EqAtom(new_var, old_term)))
            # print(f"Replacing {old_term.tex()} by {new_var.tex()}, creating an existential {existential.tex()}, flattening it recursively.")
            return existential.flatten(varsrc)

        return new_atom

    def eval(self, semantics):
        """ TODO: atoms not covered by EqAtom and RelFluents """
        return semantics.eval_atom(self)

    def nonfree_vars(self):  # generator
        return  # It's an atom
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

        symbol = Symbol("=", sorts=[args[0].sort] * 2)  # Might have to exclude this from theory's vocabulary
        Atom.__init__(self, symbol, *args)

    def eval(self, semantics):
        return semantics.eval_equality(self)

    def flatten(self, varsrc):
        """ Equality atoms are where former complex atom terms end up.
            End state of an equality atom is
              x = f(y) where all y are atomic
        """
        # print(f"Flattening equality {self.tex()}")
        new_eq = copy.deepcopy(self)

        # Both sides are atomic, nothing to do
        if new_eq.args[0].is_atomic() and new_eq.args[1].is_atomic():
            # print(f"Need not flatten {new_eq.tex()}, both sides atomic")
            return new_eq

        # Both sides are non-atomic, so must break into two equalities
        if not new_eq.args[0].is_atomic() and not new_eq.args[1].is_atomic():
            new_var = varsrc.new("z", new_eq.args[0].sort)
            return (Exists(new_var, And(EqAtom(new_eq.args[0], new_var), EqAtom(new_var, new_eq.args[1])))).flatten(
                varsrc)

        # Finally, check if one side's aguments must be flattened
        # First, decide which side is non-atomic
        i = 0
        if new_eq.args[i].is_atomic():
            i = 1

        # print(f"  Part {new_eq.args[i]} is non-atomic")
        # args[i] is non-atomic
        # Go over ITS arguments and eliminate them just like with the Atom case
        k = -1  # number of self.args[i].args member to be eliminated
        for j in range(0, len(new_eq.args[i].args)):
            if not new_eq.args[i].args[j].is_atomic():
                k = j
                break

        if k >= 0:  # found a term argument to eliminate
            # print(f"    Argument {new_eq.args[i].args[k]} must be flattened out!")
            new_var = varsrc.new("z", new_eq.args[i].args[k].sort)
            old_term = new_eq.args[i].args[k]
            new_eq.args[i].args[k] = new_var
            return (Exists(new_var, And(new_eq, EqAtom(new_var, old_term)))).flatten(varsrc)
        else:
            # print(f"    Side has no arguments to worry about!")
            return new_eq

    def simplified(self):
        lhs = self.args[0]
        rhs = self.args[1]
        if lhs.symbol.unique_name and rhs.symbol.unique_name:
            if lhs.symbol != rhs.symbol:
                return Contradiction()
            else:
                return And(*[EqAtom(a, b) for (a, b) in zip(lhs.args, rhs.args)]).simplified()
        return copy.deepcopy(self)

    def tex(self):
        return f"{self.args[0].tex()} \\eq {self.args[1].tex()}"


class Neg(Formula):  # negation
    def __init__(self, formula):
        Formula.__init__(self)
        # No constraints. Any formula can be negated.
        self.formula = formula

    def __eq__(self, other):
        return isinstance(other, Neg) and (self.formula == other.formula)

    def eval(self, semantics):
        """ TODO: atoms not covered by EqAtom and RelFluents """
        return not (semantics.eval_query(self.formula))

    def flatten(self, varsrc):
        return Neg(self.formula.flatten(varsrc))

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
            new = Neg(f_under_neg)
            #print(Back.GREEN + f"CREATING {new.tex()}: f_under_neg is {f_under_neg.__class__}" + Style.RESET_ALL)
            return new

    def vars(self, sort="any"):  # generator
        # All variables in an atom are free
        yield from self.formula.vars(sort=sort)

    def nonfree_vars(self):  # generator
        yield from self.formula.nonfree_vars()

    def symbols(self):
        yield from self.formula.symbols()

    def terms(self, sort="any"):
        yield from self.formula.terms(sort=sort)

    def atoms(self):
        yield from self.formula.atoms()

    def replace_term(self, term, new_term):
        # print(f"Negation: replacing {term.tex()} by {new_term.tex()}")
        self.formula.replace_term(term, new_term)

    def tex(self):
        if isinstance(self.formula, Junction) or isinstance(self.formula, EqAtom):
            return "\\neg ({})".format(self.formula.tex())
        else:
            return "\\neg {}".format(self.formula.tex())


class Junction(Formula):
    def __init__(self, *formulas):  # a list of formulas in junction
        Formula.__init__(self)
        self.formulas = list(formulas)

    def vars(self, sort="any"):  # generator
        for f in self.formulas:
            yield from f.vars(sort=sort)

    def nonfree_vars(self):  # generator
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
        for f in self.formulas:
            f.replace_term(term, new_term)

    def tex(self, connective):
        joiner = " \\{} ".format(connective)
        return joiner.join([f.tex() for f in self.formulas])


class And(Junction):
    def __init__(self, *formulas):
        if len(formulas) == 0:
            Junction.__init__(self, Tautology())
        else:
            Junction.__init__(self, *formulas)

    def flatten(self, varsrc):
        return And(*[f.flatten(varsrc) for f in self.formulas])

    def eval(self, semantics):
        for f in self.formulas:
            if not semantics.eval_query(f):  # If any of the conjuncts is false, the whole thing is
                return False
        return True

    def add(self, formula):
        """ Add a conjunct. If already there, do nothing """
        if formula not in self.formulas:
            self.formulas.append(formula)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        # Empty conjunctions are now ruled out in constructor.
        # In the beginning, god gathered all conjuncts under one roof.
        s_conjuncts = []  # self.formulas except for those which are themselves conjunctions, get those instead

        def unique_append(formula, alist):
            """ Adds a non-trivial conjunct to a list, ignores trivial """
            if formula not in alist and not isinstance(formula, Tautology):
                alist.append(formula)

        for f in self.formulas:
            f_s = f.simplified()  # if f is conjunction, then f_s is a flat conjunction
            if isinstance(f_s, And):  # if f was unary, then f_s is either non-unary or not a conjunction
                for f2 in f_s.formulas:  # f2 is an already-simplified nested conjunct
                    unique_append(f2, s_conjuncts)
            else:
                unique_append(f_s, s_conjuncts)

        for f in s_conjuncts:
            if isinstance(f, Contradiction):
                return f

        if len(s_conjuncts) == 0: # No disjuncts: Contradiction
            return Tautology()
        elif len(s_conjuncts) == 1:  # may still end up with a single conjunct!
            return s_conjuncts[0]

        return And(*s_conjuncts)

    def tex(self):
        texes = [f"({f.tex()})" if isinstance(f, Or) else f.tex() for f in self.formulas]
        return " \\land ".join(texes)


class Or(Junction):
    def __init__(self, *formulas):
        if len(formulas) == 0:
            Junction.__init__(self, Contradiction())
        else:
            Junction.__init__(self, *formulas)

    def flatten(self, varsrc):
        return Or(*[f.flatten(varsrc) for f in self.formulas])

    def eval(self, semantics):
        for f in self.formulas:
            if semantics.eval_query(f):  # If any of the disjuncts is true, the whole thing is
                return True
        return False

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """

        s_disjuncts = []

        def unique_append(formula, alist):
            """ Adds a non-trivial disjunct to a list, ignores trivial """
            if formula not in alist and not isinstance(formula, Contradiction):
                alist.append(formula)

        for f in self.formulas:
            f_s = f.simplified()  # if f is disjunction, then f_s is a flat disjunction
            if isinstance(f_s, Or):  # if f was unary, then f_s is either non-unary or not a disjunction
                for f2 in f_s.formulas:  # f2 is an already-simplified nested conjunct
                    unique_append(f2, s_disjuncts)
            else:
                unique_append(f_s, s_disjuncts)
        #print("s_disjuncts: " + ", ".join([str(d.tex()) for d in s_disjuncts]) + f" (while simplifying {self.tex()})")
        for f in s_disjuncts:
            if isinstance(f, Tautology):
                return f

        if len(s_disjuncts) == 0: # No disjuncts: Contradiction
            return Contradiction()
        elif len(s_disjuncts) == 1:  # may still end up with a single disjunct!
            return s_disjuncts[0]

        return Or(*s_disjuncts)

    def tex(self):
        texes = [f"({f.tex()})" if isinstance(f, And) else f.tex() for f in self.formulas]
        return " \\lor ".join(texes)


class Implies(Junction):
    def __init__(self, *formulas):
        if len(formulas) != 2:
            raise Exception("Implication must be binary!")
        Junction.__init__(self, *formulas)

    def flatten(self, varsrc):
        return Implies(*[f.flatten(varsrc) for f in self.formulas])

    def eval(self, semantics):
        if semantics.eval_query(self.formulas[0]) and not semantics.eval_query(
                self.formulas[1]):  # If any of the disjuncts is true, the whole thing is
            return False
        return True

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
        tex1 = "({})".format(self.formulas[0].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[
            0].tex()
        tex2 = "({})".format(self.formulas[1].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[
            1].tex()
        return f"{tex1} \\to {tex2}"


class Iff(Junction):
    def __init__(self, *formulas):
        if len(formulas) != 2:
            raise Exception("Bidirectional implication must be binary!")
        Junction.__init__(self, *formulas)

    def flatten(self, varsrc):
        return Iff(*[f.flatten(varsrc) for f in self.formulas])

    def eval(self, semantics):
        if semantics.eval_query(self.formulas[0]) != semantics.eval_query(self.formulas[1]):
            return False
        return True

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
        tex1 = "({})".format(self.formulas[0].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[
            0].tex()
        tex2 = "({})".format(self.formulas[1].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[
            1].tex()
        return f"{tex1} \\liff {tex2}"


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

    def __eq__(self, other):
        return self.__class__ == other.__class__ and ((self.var, self.formula) == (other.var, other.formula))

    def vars(self, sort="any"):  # generator
        yield from self.formula.vars(sort=sort)

    def nonfree_vars(self):  # generator
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

    def eval(self, semantics):
        return semantics.eval_forall(self)

    def flatten(self, varsrc):
        return Forall(copy.deepcopy(self.var), self.formula.flatten(varsrc))

    def simplified(self):
        """ Returns a shallow syntactic simplification of self
            Don't bother simplifying quantifiers for now """
        f_simplified = self.formula.simplified()
        if isinstance(f_simplified, Contradiction) or isinstance(f_simplified, Tautology):
            return f_simplified
        elif isinstance(f_simplified, Junction):
            # EXPERIMENTAL!!!
            # Purpose: Minimize the scope of the quantifier
            pass

            # END

        return Forall(copy.deepcopy(self.var), f_simplified)

    def tex(self):
        return Quantified.tex(self, "forall")


class Exists(Quantified):
    """ \\exists var (formula) """

    def __init__(self, var, formula):
        Quantified.__init__(self, var, formula)

    def eval(self, semantics):
        return semantics.eval_exists(self)

    def flatten(self, varsrc):
        new_var = copy.deepcopy(self.var)
        new_f = self.formula.flatten(varsrc)
        # print(f"Flattening {self.tex()}: new var {new_var.tex()}, new sub {new_f.tex()}")
        return Exists(new_var, new_f)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self
            Don't bother simplifying quantifiers for now """
        f_simplified = self.formula.simplified()

        if isinstance(f_simplified, Contradiction) or isinstance(f_simplified, Tautology):
            return f_simplified
        elif isinstance(f_simplified, And) or isinstance(f_simplified, Or):
            # EXPERIMENTAL!!!
            # Purpose: Minimize the scope of the quantifier
            f_inscope = []
            f_outscope = []
            for f in f_simplified.formulas:
                if self.var in f.free_vars():
                    f_inscope.append(f)
                else:
                    f_outscope.append(f)
            if len(f_inscope) == 0:  # nothing in scope, remove quantifier
                return f_simplified
            elif len(f_outscope) > 0:  # some inscope, some out
                juncts = f_outscope + [Exists(copy.deepcopy(self.var), f_simplified.__class__(*f_inscope))]
                return f_simplified.__class__(*juncts).simplified()
            else:  # all in scope
                # print(f"All in scope for {self.tex()}")
                if isinstance(f_simplified, And) and len(f_simplified.formulas) > 1:  # if a non-unary conjunction
                    # print("  Non-unary conjunction")
                    term = None  # Term to replace self.var in rest
                    rest = []  # Rest of conjuncts, to be preserved after replacing self.var by rest
                    found_elim = False
                    for conj in f_simplified.formulas:
                        if isinstance(conj,
                                      EqAtom) and self.var in conj.args and not found_elim:  # and if there is an equality atom about self.var
                            # print(f"    There is an equality atom about self.var")
                            term = conj.args[0]
                            if term == self.var:
                                term = conj.args[1]  # Get the term on the other side of the equality
                            # print(f"      term becomes {term.tex()}")
                            found_elim = True
                        else:  # not an equality conjunct, store it
                            rest.append(conj)
                    # print(f"    Ended up with term={term} and rest={rest}")
                    if not term is None and len(rest) > 0:
                        # print(f"    About to replace {self.var.tex()} by {term.tex()}")
                        # Get rid of the equality and substitute term for self.var in the rest
                        for r in rest:
                            r.replace_term(self.var, term)
                        return And(*rest).simplified()
                    # else, fall back on default return
        elif isinstance(f_simplified, EqAtom) and (self.var in f_simplified.args):
            # Also experimental
            # Purpose: eliminate trivial statements \exists x(x = TERM)
            # Every term has an interpretation, so asserting its existence is a tautology
            return Tautology()

        return Exists(copy.deepcopy(self.var), f_simplified)

    def tex(self):
        return Quantified.tex(self, "exists")


class Axiom(object):
    """ An axiom contains a formula, but also has specialized creation mechanisms and ways to maintain its syntactic invariant
    """

    def __init__(self):
        # Every axiom has a formula
        self.formula = None

    def tex(self):
        return self.formula.tex()


class Theory:
    """ A vocabulary and a set of formulas over that vocabulary.
        Maintains a map of all mentions of each symbol.
        Handles the creation of legal formulas (wff).
        Can either add new formulas to itself,
        or just returns without adding, to be used for regression.

        Generic class, so allows arbitrary sorts
    """

    def __init__(self, name, sorts=(), subsets=()):
        self.name = name
        self.semantics = None
        # Let's agree to have just one arity and type per symbol name
        # There is literally no downside to this
        self.sorts = ["reals", "object", None]  # Default sorts. None is for predicates
        self.constants = {}  # sort -> [list of symbols of this sort mentioned in the theory so far]
        for s in sorts:  # Custom sorts
            self.add_sort(s)

        # For each sort, including custom ones, prepare a bag for constants
        for s in self.sorts:
            self.constants[s] = []

        # self.vocabulary = {} # Maps symbol_name to Symbol
        # self.vocabulary["="] = Symbol("=", sort="situation")
        # add arithmetics here?
        # self.vocabulary["+"] = Symbol("+", sort="reals", sorts=["reals", "reals"], infix=True)
        # self.vocabulary["-"] = Symbol("-", sort="reals", sorts=["reals", "reals"], infix=True)
        # self.vocabulary["*"] = Symbol("*", sort="reals", sorts=["reals", "reals"], infix=True)
        # self.vocabulary["/"] = Symbol("/", sort="reals", sorts=["reals", "reals"], infix=True)
        # self.vocabulary["^"] = Symbol("^", sort="reals", sorts=["reals", "reals"], infix=True)

        self.axioms = {"default": set()}  # Sets of Formula objects (no free variables)
        # It's a dict because we want to allow one to categorize axioms into subsets.
        for subset in subsets:
            self.axioms[subset] = set()
        # self.occurs = {} # A map from vocabulary to sentences with occurrences

    def add_sort(self, new_sort):
        if new_sort in self.sorts:
            raise TypeError("Cannot add sort '{}'".format(new_sort))
        self.sorts.append(new_sort)
        self.constants[new_sort] = []

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

    def add_axiom(self, axiom, force=False, where="default"):  # force means force-add unknown symbols to vocab.
        """ Formula must be a sentence over the vocabulary """
        # Check if every symbol used in the formula
        # (including quantified variables, because they may not occur
        # anywhere as arguments) is in theory's vocabulary
        if not isinstance(axiom, Axiom):
            raise Exception(f"Object {axiom.tex()} ({axiom.__class__}) is not an axiom, cannot add!")

        if axiom in self.axioms[where]:
            raise Exception("Axiom already a part of theory!")

        for s in axiom.formula.symbols():
            # if s not in self.vocabulary.values():
            #     if not force:
            #         raise Exception("Symbol {} is not in {}'s vocabulary!".format(s.name, self.name))
            #     else:
            #         print("Warning: forcing new symbol {} into vocabulary".format(s.name))
            #         self.add_symbol(s)
            if not s.is_var and len(s.sorts) == 0 and not s.sort is None:
                self.constants[s.sort].append(s)

        self.axioms[where].add(axiom)

    def add_semantics(self, semantics):
        print(f"Adding semantics to theory {self.name}. This assumes all axioms are already in.")
        self.semantics = semantics

    def print_vocabulary(self):
        print("Vocabulary of theory '{}':".format(self.name))
        for s_n, s in self.vocabulary.items():
            print("  \t{}".format(str(s)))


class VarSource(object):
    """ A source of fresh variables of whatever sort;
        useful when accessed from multiple namespaces """

    def __init__(self):
        self.sorts = {}  # basename -> sort (only one sort per basename)
        self.counts = {}  # basename -> count

    def new(self, basename="z", sort="object"):
        if basename not in self.sorts:
            if basename in self.counts:
                raise Exception("Var source integrity violation")
            self.sorts[basename] = sort
            self.counts[basename] = 1
        var = Term(Symbol(f"{basename}_{{{self.counts[basename]}}}", sort=sort, is_var=True))
        self.counts[basename] += 1
        return var
