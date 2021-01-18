from formula import *

def legal_name(n):
    #if not n.isalpha():
    #    raise Exception("Bad name '{}'".format(n))
    return n


class Axiom(object):
    """ An axiom contains a formula, but also has specialized creation mechanisms and ways to maintain its syntactic invariant
    """
    def __init__(self):
        # Every axiom has a formula
        self.formula = None

        # The Axiom class provides a way to build said formula

class SSA(Axiom):
    """ Common to all SSA: form
        \\forall \\bar{x} \\forall a \forall s ([Atom(\bar{x}, do(a,s))] <-> Phi(\bar{x},a,s))
        Atom is either a relational fluent atom or an equality about a functional fluent and variable y (part of \bar{x} in form above)
    """
    pass

class RelSSA(SSA):
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

        self.a_var = voc['a']
        self.s_var = voc['s']
        # Create universally quantified variables
        lhs_atom_args = obj_vars + [voc['do(a,s)']]
        rhs_atom_args = obj_vars + [voc['s']]

        self.obj_vars = obj_vars
        self.univ_vars = obj_vars + [voc['a'], voc['s']]
        self.lhs = Atom(symbol, *lhs_atom_args)
        self.frame_atom = Atom(symbol, *rhs_atom_args)
        self.pos_effects = []
        self.neg_effects = []
        self.formula = None # this is just to indicate where the formula can be found
        self._build_formula() # reconcile bits into one formula


    def _build_formula(self):
        p_eff = Or(*self.pos_effects)
        n_eff = Or(*self.neg_effects)
        frame = And(self.frame_atom, Neg(n_eff))
        rhs = Or(p_eff, frame)
        iff = Iff(self.lhs, rhs)

        quantified = iff
        for var in reversed(self.univ_vars):
            quantified = Forall(var, quantified)

        self.formula = quantified.simplified()

        if not self.formula.is_sentence():
            raise Exception("Resulting SSA is not a sentence. Perhaps an extra var in effects?")

    def _effect_type_check(self, action, context):
        if not isinstance(action, Term) or action.sort != "action":
            raise TypeError(f"Bad action term {action.tex()}!")
        if not isinstance(context, Formula):
            raise TypeError(f"Bad context formula {context.tex()}!")
        for a_arg in action.args:
            if a_arg.sort != "object":
                raise TypeError(f"Action term {action.tex()} has non-object arguments!")

    def _add_effect(self, action, context, positive=True):
        """ action: fully instantiated action term with variables among obj_vars
                (other vars will be existentially quantified, automatically)
            context: arbitrary formula uniform in s with free variables among obj_vars
            (a=action_name(\bar{x}) \land \Phi(\bar{x},s))
        """
        self._effect_type_check(action, context)
        eq = EqAtom(self.a_var, action)
        effect = And(eq, context)
        # All vars not occurring on LHS will get existentially quantified
        for v in effect.free_vars():
            if v not in self.univ_vars:
                effect = Exists(v, effect)

        effect = effect.simplified()
        if not effect.uniform_in(self.s_var):
            raise Exception(f"Effect {effect.tex()} not uniform in s!")

        if positive:
            self.pos_effects.append(effect)
        else:
            self.neg_effects.append(effect)
        self._build_formula()

    def add_pos_effect(self, action, context):
        self._add_effect(action, context, positive=True)


    def add_neg_effect(self, action, context):
        self._add_effect(action, context, positive=False)

    def describe(self):
        self.formula.describe()

    def tex(self):
        return self.formula.tex()



class FuncSSA(SSA): # Version with no common ancestor w/ RelSSA
    # In truth, these axioms should not be chilren of formulas. We need a new superclass, something like Axiom.
    # Every axiom is in the end a formula, but it is not part of the inductive definition of formulas.
    """ Successor state axiom for a functional fluent
        Custom-form FOL formula for Basic Action Theories
        Constructor only takes a functional fluent symbol and terms for variables
        The RHS is constructed sequentially by adding effects
    """
    def __init__(self, symbol, obj_vars=[], voc={}):
        """ Classic Reiter's SSA
            f(\\bar{x}, do(a,s)) = y \liff [disj. of effects wrt y] \lor y = f(\bar{x}, s)
              \land \neg \exists y' [disj. of effects wrt y']
            obj_vars are the \\bar{x}
            voc is the vocabulary containing terms 'do(a,s)', 'a', 's'
            y and y' are created here, not passed as arguments
        """
        if not isinstance(symbol, FuncFluentSymbol):
            raise Exception("A functional SSA must be about a functional fluent")

        for v in obj_vars:
            if v.sort != "object":
                raise TypeError("Fluent object arguments must be of sort object")

        # Remember the important standard symbols for easy access
        self.a_var = voc['a']
        self.s_var = voc['s']

        # Create universally quantified variables for the fluent eq-atom on both sides
        self.lhs_atom_args = obj_vars + [voc['do(a,s)']]
        self.rhs_atom_args = obj_vars + [voc['s']]


        # The RHS of equality, the distinguished y and y' variables
        # Must check for collisions with object variables and with effect variables (even if quantified?)
        self.y = Term(Symbol("y", sort=symbol.sort, is_var=True))
        self.y_ = Term(Symbol("y'", sort=symbol.sort, is_var=True))

        if self.y.name in [v.name for v in obj_vars]:
            # This is, in fact, allowed in first-order logic - having two variables of same name but different Sorts
            # However, they will look identical in formulas, so let's rule this out
            raise Exception("Variable 'y' is reserved in functional SSA! Can't use for an argument.")

        # \bar{x} - just the object argument variables
        self.obj_vars = obj_vars
        # All implicitly quantified variables
        self.univ_vars = obj_vars + [self.y, voc['a'], voc['s']]

        # Build the actual func. fluent terms
        self.lhs_fluent = Term(symbol, *self.lhs_atom_args)
        self.rhs_fluent = Term(symbol, *self.rhs_atom_args)
        # LHS equality
        self.lhs = EqAtom(self.lhs_fluent, self.y)
        # RHS equality
        self.frame_atom = EqAtom(self.y, self.rhs_fluent)

        # For func. fluents, all effects are both positive and negative
        self.effects = []

        self.formula = None # this is just to indicate where the formula can be found
        self._build_formula() # reconcile bits into one formula

    def simplified(self):
        raise Exception("Not supposed to do this on a SSA")
        # Do what then? Get a plain FOL version from self.formula and do whatever

    def _build_formula(self):
        print("\nWill build formula from effects")
        effects_copy = copy.deepcopy(self.effects)
        print(f"Effects copied. Check: {len(self.effects)} == {len(effects_copy)}")
        #effects_copy = [copy.deepcopy(e) for e in self.effects]
        for e in self.effects:
            print(f"    (+): {e.tex()}", e)
        for e in effects_copy:
            print(f"    (-): {e.tex()}", e)
        print("(end of listing)")

        p_eff = Or(*self.effects)

        # Protection from side effects of substitution
        # Maybe make all term methods return-only, like .simplified()?

        n_eff = Or(*effects_copy)
        print(f"    (-) {n_eff.tex()}")
        n_eff.replace_term(self.y, self.y_) # Replace y by y'
        print(f"    (-) same, y/y': {n_eff.tex()}")

        print("\nAll effects are now ready")
        print("Positive: ", p_eff.tex())
        #p_eff.describe()
        print("Negative: ", n_eff.tex())
        #n_eff.describe()

        frame = And(self.frame_atom, Neg(Exists(self.y_, n_eff)))
        rhs = Or(p_eff, frame)
        iff = Iff(self.lhs, rhs)

        quantified = iff
        for var in reversed(self.univ_vars):
            quantified = Forall(var, quantified)

        self.formula = quantified.simplified()

        if not self.formula.is_sentence():
            #self.formula.describe()
            raise Exception("Resulting SSA is not a sentence. Perhaps an extra var in effects?")

    def _effect_type_check(self, action, context):
        if not isinstance(action, Term) or action.sort != "action":
            raise TypeError(f"Bad action term {action.tex()}!")
        if not isinstance(context, Formula):
            raise TypeError(f"Bad context formula {context.tex()}!")
        for a_arg in action.args:
            if a_arg.sort != "object":
                pass
                # Can't remember why only object args are allowed. Why?
                #raise TypeError(f"Action term {action.tex()} has non-object arguments!")

    def add_effect(self, action, context):
        """ action: fully instantiated action term with variables among obj_vars
                (other vars will be existentially quantified, automatically)
            context: arbitrary formula uniform in s with free variables among obj_vars
            (a=action_name(\bar{x}) \land \Phi(\bar{x},s))
            EFFECT MUST MENTION y!!!!!!!!
        """
        print(f"Adding effect: action is {action.tex()}, context is {context.tex()}")
        self._effect_type_check(action, context)
        eq = EqAtom(self.a_var, action)
        effect = And(eq, context)
        print(f"Becomes a formula: {effect.tex()}")
        effect.describe()
        # All vars not occurring on LHS will get existentially quantified
        # all except the special variable y
        for v in set(effect.free_vars()):
            if v not in self.univ_vars:
                effect = Exists(v, effect)

        effect = effect.simplified()

        print(f"Add existentials and simplify: {effect.tex()}")

        if not effect.uniform_in(self.s_var):
            raise Exception(f"Effect {effect.tex()} not uniform in s!")
        if self.y not in effect.free_vars():
            raise Exception("Effect does not have a free 'y' variable!")


        self.effects.append(effect)
        self._build_formula()

    def describe(self):
        self.formula.describe()

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
    def __init__(self, name, sorts=[], subsets=[]):
        self.name = legal_name(name)
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
        #self.vocabulary = {}
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
        if (isinstance(formula, RelSSA) or isinstance(formula, FuncSSA)): # and formula.finalized: # Correct class implies finalized
            self.axioms["ss"].add(formula)
        else:
            raise Exception("Not a proper SSA, cannot add to theory")


class HybridTheory(BasicActionTheory):
    """ Adds new axiom class: D_{sea} """
    def __init__(self, name):
        Theory.__init__(self, name)
