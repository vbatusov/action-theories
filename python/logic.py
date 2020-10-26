def good_sort(s):
    return s in ["action", "object", "situation", "reals", "time"]
def good_symbol_type(t):
    return t in ["predicate", "function", "variable", "constant", "number"]

def sort_check(s):
    if not good_sort(s):
        raise Exception("Bad sort {}".format(s))
    return s

def check_arg_sorts(symbol, args):
    if len(args) != symbol.arity:
        raise Exception("Wrong number of arguments - {} instead of {}!".format(len(args), symbol.arity))

    for s_sort, arg in zip(symbol.sorts, args):
        if s_sort != arg.sort():
            raise Exception("Wrong argument sort. Expecting {}, got {}!".format(s_sort, arg.sort()))
    return args

# namespace: {name -> symbol}
# if name already exists, make sure

def name_check(n, namespace=None):
    return n






class Symbol:
    """ Any alph string
        must have
            - type (pred, func) (inferred)
            - a list of arg sorts (and, implicitly, arity)
            - return sort (if func)
    """
    def __init__(self, name, sorts=[], sort=None, infix=False, var=False):

        # If no return sort, assume it's a predicate
        if not sort:
            self.type = "predicate"
        else:
            if not good_sort(sort):
                raise Exception("Bad function sort {}".format(sort))
            if var:
                self.type = "variable"
            elif len(sorts) > 0:
                self.type = "function"
            else:
                self.type = "constant"

        for s in sorts:
            if not good_sort(s):
                raise Exception("Bad argument sort {}".format(s))

        if infix and len(sorts) != 2:
            raise Exception("An infix symbol must be binary, and this one is {}-ary".format(len(sorts)))

        self.name = name
        self.sorts = sorts
        self.arity = len(sorts)
        self.sort = sort
        self.is_var = (self.type == "variable")
        self.infix = infix

    def __str__(self):
        #repr_args = [arg if arg else "[{}]".format(sort) for (arg, sort) in zip(self.args, self.sorts)]
        strargs = ""
        if self.arity > 0:
            strargs = "({})".format(", ".join(["<{}>".format(s) for s in self.sorts]))
        retsort = ""
        if self.type != "predicate":
            retsort = " : <{}>".format(self.sort)
        return "{}{}{}".format(self.name, strargs, retsort)


class Term: #
    """ A term built using variables and function symbols
        For ease of use, construction should infer sorts from arguments
        Can construct term via args and sort, and infer term's symbol, if necessary
     """
    # Term(Symbol, [Term, Term, ...])
    def __init__(self, symbol, args=[]):
        self.symbol = symbol
        self.is_var = symbol.is_var
        self.args = check_arg_sorts(symbol, args)

    def __eq__(self, other):
        #print("Inside __eq__!!!")
        # Let's see
        # Compare symbols by instance --- must keep them in good order
        # Compare terms by recursively comparing underlying symbols
        if self.symbol is other.symbol:
            # If same symbol, can safely assume arities match
            for arg1, arg2 in zip(self.args, other.args):
                if arg1 != arg2: # Recursively invoke comparison
                    return False
            return True
        else:
            return False

    def sort(self):
        return self.symbol.sort

    def arity(self):
        return self.symbol.arity

    def name(self):
        return self.symbol.name

    def mentions_term(self, term):
        # either self is itself equal to term, or one of its argments mentions it
        # print("\nPython comparisons!!!")
        # print("Comparing")
        # print(str(self))
        # print("against")
        # print(str(term))

        if self == term:
            return True

        for arg in self.args:
            if arg.mentions_term(term):
                return True

        #print("NOT EQUAL\n\n")
        return False

    def mentions_symbol(self, symbol):
        raise Exception("Feature not implemented yet")

    def __str__(self):
        return self.tex()

    def tex(self):
        if self.symbol.infix: # binary, already checked
            return self.name().join([arg.tex() for arg in self.args])
        if self.arity() == 0:
            return self.name()
        return "{}({})".format(self.symbol.name, ", ".join([arg.tex() for arg in self.args]))


# class Var(Term):
#     def __init__(self, name, sort="object"):
#         Term.__init__(self, name, sort)
#         self.is_var = True

# class Var: # THis is a questionable class. Why not have it as a term?
#     """ Note: must maintain a namespace???
#         cannot have identically named variables and constants
#     """
#     def __init__(self, name, sort="object"):
#         self.name = name_check(name)
#         self.sort = sort_check(sort)
#         self.arity = 0
#         self.sorts = []
#         self.infix = False
#
#     def __str__(self):
#         return "var {} : {}".format(self.name, self.sort)
#
#     def tex(self):
#         return self.name

class Formula(object):
    """ Any FOL wff """
    def __init__(self):
        pass

class Atom(Formula):
    """ Atomic formula """
    def __init__(self, symbol, args=[]): # args are Terms
        Formula.__init__(self)
        if symbol.type != "predicate":
            raise Exception("Cannot make an atom out of {}".format(str(symbol)))
        self.symbol = symbol
        self.args = check_arg_sorts(symbol, args)

    def quantifies_over(self, var_term):
        # Atom cannot contain a quantifier
        return False

    def mentions_term(self, term):
        for arg in self.args:
            if arg.mentions_term(term):
                return True
        return False

    def mentions_symbol(self, symbol):
        raise Exception("Feature not implemented yet")


    def tex(self):
        if len(self.args) > 0:
            return "{}({})".format(self.symbol.name, ", ".join([arg.tex() for arg in self.args]))
        return self.symbol.name

class Neg(Formula): # negation
    def __init__(self, formula):
        Formula.__init__(self)
        # No constraints. Any formula can be negated.
        self.formula = formula

    def quantifies_over(self, var_term):
        return (self.formula.quantifies_over(var_term))

    def mentions_term(self, term):
        return self.formula.mentions_term(term)

    def tex(self):
        return "\\neg ({})".format(self.formula.tex())

class Junction(Formula):
    def __init__(self, formulas): # a list of formulas in junction
        Formula.__init__(self)
        if len(formulas) < 2:
            raise Exception("A binary connective needs at least two formulas!")
        # No constraints. Any formula can be negated.
        self.formulas = formulas

    def quantifies_over(self, var_term):
        for f in self.formulas:
            if f.quantifies_over(var_term):
                return True
        return False

    def mentions_term(self, term):
        for f in self.formulas:
            if f.mentions_term(term):
                return True
        return False

    def tex(self, connective):
        joiner = " \\{} ".format(connective)
        return joiner.join([f.tex() for f in self.formulas])

# class To(Junction) # Strictly binary

# class Liff(Junction)  # Strictly binary

class And(Junction):
    def __init__(self, formulas):
        Junction.__init__(self, formulas)

    def tex(self):
        return Junction.tex(self, "land")

class Or(Junction):
    def __init__(self, formulas):
        Junction.__init__(self, formulas)

    def tex(self):
        return Junction.tex(self, "lor")

class Quantified(Formula):
    """ <quantifier> var (formula) """
    def __init__(self, var, formula):
        Formula.__init__(self)
        # var should be a Variable
        # formula should be a well-formed formula
        # formula cannot quantify over var (throw exc.)
        if not var.is_var:
            raise Exception("{} is not a variable, cannot quantify over it!".format(str(var)))
        self.var = var
        if formula.quantifies_over(var):
            raise Exception("Formula {} already quantifies over {}".format(formula.tex(), var.tex()))
        if not formula.mentions_term(var):
            print("Warning: formula {} does not have free {} to quantify over!".format(formula.tex(), var.tex()))
        self.formula = formula

    def quantifies_over(self, var_term):
        return (var_term == self.var or self.formula.quantifies_over(var_term))

    def mentions_term(self, term):
        return self.formula.mentions_term(term)

    def tex(self, quantifier):
        return "\\{} {}({})".format(quantifier, self.var.tex(), self.formula.tex())

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

class Theory:
    """ A vocabulary and a set of formulas over that vocabulary.
        Maintains a map of all mentions of each symbol.
        Handles the creation of legal formulas (wff).
        Can either add new formulas to itself,
        or just returns without adding, to be used for regression.
    """
    def __init__(self, name):
        self.name = name
        self.vocabulary = set() # A set of Symbol objects
        self.formulas = set() # A set of Formula objects (no free variables)
        self.occurs = {} # A map from vocabulary to sentences with occurrences

    def add_symbol(self, symbol):
        if symbol not in self.vocabulary:
            self.vocabulary.add(symbol)
        else:
            print("Symbol {} already in vocabulary".format(str(symbol)))

    def print_vocabulary(self):
        print("Vocabulary of Theory {}:".format(self.name))
        for s in self.vocabulary:
            print("  {} \t{}".format(s.type, str(s)))

#s_pred = Symbol('P', sorts=["object", "time", "situation"])
#s_obj = Symbol('c', type="function", sorts=[], sort="object")
#s_time = Symbol('t', type="variable", sort="time")
#symbols = [s_pred, s_obj, s_time]
#s = Symbol('P')
#a = Atom(args=[s_obj, s_time])

#print("Symbols: {}".format(", ".join([str(s) for s in symbols])))


# What do I even want?
# Create FOL and SOL formulas and regress them
# Desirable: invoke prolog and ODE solver to actually compute answers
# Something like:
# # Define vocabulary (all symbols used):
# # Idea: don't define variables; just assume an undefined symbol is a variable; infer sort from usage
theory = Theory("test")


h = Symbol("h", sorts=["object", "time", "situation"], sort="reals") # Inferred to be a temp fluent
c = Symbol("C", sorts=["object", "situation"]) # Context predicate
p = Symbol("P", sorts=["object"])
x = Symbol("x", sort="object", var=True)
do = Symbol("do", sorts=["action","situation"], sort="situation")
s_0 = Symbol("S_0", sort="situation")
a_noop = Symbol("sleep", sorts=["time"], sort="action")
tau = Symbol("\\tau", sort="time")
sigma = Symbol("\\sigma", sort="situation")
s = Symbol("s", sort="situation", var=True)


theory.add_symbol(h)
theory.add_symbol(c)
theory.add_symbol(x)
theory.add_symbol(p)

theory.print_vocabulary()

sitterm = Term(do, [Term(a_noop, [Term(tau)]), Term(s_0)])
term = Term(h, [Term(x), Term(tau), sitterm])
print("h(x,\\tau, do(sleep(\\tau), S_0)) -> ", term.tex())

c_atom = Atom(c, [Term(x), sitterm])
print("C(x, ...) -> ", c_atom.tex())

allxc = Forall(Term(x), c_atom)
print("\\forall x (C(...)) -> ", allxc.tex())

AsExC = Forall(Term(x), Exists(Term(s), Neg(Atom(c, [Term(x), Term(s)]))))
print("\\forall x \\exists s (C(x,s)) -> ", AsExC.tex())

disj = Or([Atom(p, [Term(x)]), Neg(Atom(c, [Term(x), Term(s)]))]) #Or([Atom(p, [Term(x)]), Atom(p, [Term(x)])])
print(str(disj))
print("P(x) \\lor \\neg (C(x,s)) -> ", disj.tex())
# # Build the formula:

# y = Var("y", sort="reals")
# t = Var("t", sort="time")
# s = Var("s", sort="situation")
# lhs = Equals(Term(h, [x, t, s]), y)
# tca1 = And(Atom(c, [x, s]), Equals(y, tca1math))
# tca2 = And(Not(Atom(c, [x,s ])), Equals(y, tca2math))
# rhs = Or(tca1, tca2)
# iff = Iff(lhs, rhs)
# sea = Forall(x, Forall(y, Forall(t, Forall(s, iff))))


# for s in [h, c, x]:
#     print(str(s), repr(s))
