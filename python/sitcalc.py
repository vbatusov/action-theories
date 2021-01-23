from fol import *
from colorama import Fore, Back, Style  # Pretty printing

class Sitcalc(object):
    """ Stores common sitcalc symbols and terms """
    # Formerly known as self.special_symbols
    sym = {}
    # Formerly known as self.special_terms
    term = {}

    def __populate__():
        Sitcalc.sym = {
            "S_0" : Symbol("S_0", sort="situation"),
            "a" : Symbol("a", sort="action", is_var=True),
            "s" : Symbol("s", sort="situation", is_var=True),
            "do" : Symbol("do", sort="situation", sorts=["action", "situation"]),
            "Poss" : Symbol("Poss", sorts=["action", "situation"]),
        }

        Sitcalc.term = {
            "S_0" : SitTerm(Sitcalc.sym["S_0"]),
            "a" : Term(Sitcalc.sym["a"]),
            "s" : SitTerm(Sitcalc.sym["s"]),
        }
        Sitcalc.term["do(a,s)"] = SitTerm(Sitcalc.sym["do"], Sitcalc.term["a"], Sitcalc.term["s"])


class ActionTerm(Term):
    def __init__(self, name, *args):
        """ Can quickly create actions without creating a symbol """
        arg_sorts = [arg.sort for arg in args]
        Term.__init__(self, Symbol(name, sort="action", sorts=arg_sorts), *args)

class SitTerm(Term): #
    """ A situation term; can be any one of:
            - a variable of sort situation,
            - constant S_0
            - any term build using do(-,-)
        The whole point of this class is to encapsulate situation-specific operations without
        cluttering up pure FOL notions with situation calculus
    """
    def __init__(self, symbol, *args):
        if not symbol.sort=="situation":
            raise TypeError("To create a situation term, symbol must be of sort situation.")
        if not symbol.is_var and not symbol==Sitcalc.sym["S_0"] and not symbol==Sitcalc.sym["do"]:
            raise TypeError(f"Cannot create a situation term out of symbol {symbol}")
        Term.__init__(self, symbol, *args)

    def previous_sit(self):
        """ returns the immediately previous situation, if possible """
        if self.is_var or self.symbol == Sitcalc.sym["S_0"]:
            return None
        return self.args[1]

    def terms(self, sort="any"):
        """ Overrides that of Term, only returns top-level sit """
        if sort == "any" or self.sort == sort:
            yield self

class PossAtom(Atom):
    """ Poss atoms are special, all reuse the same symbol and have arg number and sorts.
        Have additional functionality, too.
     """
    def __init__(self, action_arg, sit_arg):
        if action_arg.sort != "action" or sit_arg.sort != "situation":
            raise TypeError("Poss atom argument sorts violation")
        Atom.__init__(self, Sitcalc.sym["Poss"], action_arg, sit_arg)
        self.action_term = self.args[0]
        self.sit_term = self.args[1]

class Axiom(object):
    """ An axiom contains a formula, but also has specialized creation mechanisms and ways to maintain its syntactic invariant
    """
    def __init__(self):
        # Every axiom has a formula
        self.formula = None

    def tex(self):
        return self.formula.tex()


class InitAxiom(Axiom):
    """ Any FOL sentence uniform in S_0 """
    def __init__(self, formula):
        Axiom.__init__(self)
        if not formula.is_sentence():
            raise Exception(f"Init axiom must be a sentence, and this isn't: {formula.tex()}")
        if not formula.uniform_in(Sitcalc.term["S_0"]):
            raise Exception("Init axiom must be uniform in S_0")
        self.formula = formula


class APA(Axiom):
    """ An action precondition axiom in regular situation calculus.
        defined by:
          A formula of the form Poss(A(x),s) <-> Pi_A(x,s)
        stored as:
          action term A(x,s)
          right-hand side Pi_A(x,s)
        generates:
          a proper FOL representation
    """
    def __init__(self, action_term, rhs=Tautology()):
        Axiom.__init__(self)
        self.action = action_term.symbol
        self.poss_atom = PossAtom(action_term, Sitcalc.term["s"])
        self.rhs = rhs
        for rhs_var in rhs.free_vars():
            if rhs_var not in self.poss_atom.free_vars():
                raise Exception(f"Variable {rhs_var.tex()} from RHS is not among the variables in Poss!!")
        self.formula = None
        self._build_formula()

    def _build_formula(self):
        f = Iff(self.poss_atom, self.rhs).simplified()
        self.formula = f.close()

    def instantiate_rhs(self, poss_atom):
        """ Returns the right-hand side with variables instantiated as in poss_atom (can assume it's PossAtom)
        """
        old_vars = self.poss_atom.action_term.args + [self.poss_atom.sit_term]
        new_vars = poss_atom.action_term.args + [poss_atom.sit_term] # in exactly the same order
        return self.rhs.apply_substitution(old_vars, new_vars)

class SSA(Axiom):
    """ Common to all SSA: form
        \\forall \\bar{x} \\forall a \forall s ([Atom(\bar{x}, do(a,s))] <-> Phi(\bar{x},a,s))
        Atom is either a relational fluent atom or an equality about a functional fluent and variable y (part of \bar{x} in form above)
    """
    def __init__(self):
        Axiom.__init__(self)

class RelSSA(SSA):
    """ Successor state axiom for a relational fluent
        Custom-form FOL formula for Basic Action Theories
        Constructor only takes a relational fluent symbol and terms for variables (excluding situation arg)
        The RHS is constructed sequentially by adding positive and negative effects
    """
    def __init__(self, symbol, obj_vars=[]):
        """ Classic Reiter's SSA
            F(\\bar{x}, do(a,s)) \liff [disj. of pos. effects] \lor F(\bar{x}, s)
              \land \neg [disj. of neg. effects]
            obj_vars are the \\bar{x}
        """
        SSA.__init__(self)
        # Must maintain the pieces and the total formula in sync!
        if not isinstance(symbol, RelFluentSymbol):
            raise Exception("A relational SSA must be about a relational fluent")

        for v in obj_vars:
            if v.sort != "object":
                raise TypeError("Fluent object arguments must be of sort object")

        self.a_var = Sitcalc.term['a']
        self.s_var = Sitcalc.term['s']
        # Create universally quantified variables
        lhs_atom_args = obj_vars + [Sitcalc.term['do(a,s)']]
        rhs_atom_args = obj_vars + [Sitcalc.term['s']]

        self.obj_vars = obj_vars
        self.univ_vars = obj_vars + [Sitcalc.term['a'], Sitcalc.term['s']]
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

    def add_pos_effect(self, action, context=Tautology()):
        self._add_effect(action, context, positive=True)

    def add_neg_effect(self, action, context=Tautology()):
        self._add_effect(action, context, positive=False)

    def describe(self):
        self.formula.describe()

    def tex(self):
        return self.formula.tex()



class FuncSSA(SSA):
    """ Successor state axiom for a functional fluent
        Custom-form FOL formula for Basic Action Theories
        Constructor only takes a functional fluent symbol and terms for variables
        The RHS is constructed sequentially by adding effects
    """
    def __init__(self, symbol, obj_vars=[]):
        """ Classic Reiter's SSA
            f(\\bar{x}, do(a,s)) = y \liff [disj. of effects wrt y] \lor y = f(\bar{x}, s)
              \land \neg \exists y' [disj. of effects wrt y']
            obj_vars are the \\bar{x}
            y and y' are created here, not passed as arguments
        """
        SSA.__init__(self)
        if not isinstance(symbol, FuncFluentSymbol):
            raise Exception("A functional SSA must be about a functional fluent")

        for v in obj_vars:
            if v.sort != "object":
                raise TypeError("Fluent object arguments must be of sort object")

        # Remember the important standard symbols for easy access
        self.a_var = Sitcalc.term['a']
        self.s_var = Sitcalc.term['s']

        # Create universally quantified variables for the fluent eq-atom on both sides
        self.lhs_atom_args = obj_vars + [Sitcalc.term['do(a,s)']]
        self.rhs_atom_args = obj_vars + [Sitcalc.term['s']]


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
        self.univ_vars = obj_vars + [self.y, Sitcalc.term['a'], Sitcalc.term['s']]

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
        effects_copy = copy.deepcopy(self.effects)

        p_eff = Or(*self.effects)
        n_eff = Or(*effects_copy)
        n_eff.replace_term(self.y, self.y_) # Replace y by y'

        frame = And(self.frame_atom, Neg(Exists(self.y_, n_eff)))
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
                pass
                # Can't remember why only object args are allowed. Why?
                #raise TypeError(f"Action term {action.tex()} has non-object arguments!")

    def add_effect(self, action, context=Tautology()):
        """ action: fully instantiated action term with variables among obj_vars
                (other vars will be existentially quantified, automatically)
            context: arbitrary formula uniform in s with free variables among obj_vars
            (a=action_name(\bar{x}) \land \Phi(\bar{x},s))
            EFFECT MUST MENTION y!!!!!!!!
        """
        #print(f"Adding effect: action is {action.tex()}, context is {context.tex()}")
        self._effect_type_check(action, context)
        eq = EqAtom(self.a_var, action)
        effect = And(eq, context)
        #print(f"Becomes a formula: {effect.tex()}")
        #effect.describe()
        # All vars not occurring on LHS will get existentially quantified
        # all except the special variable y
        for v in set(effect.free_vars()):
            if v not in self.univ_vars:
                effect = Exists(v, effect)

        effect = effect.simplified()

        #print(f"Add existentials and simplify: {effect.tex()}")

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


class BasicActionTheory(Theory):
    """ Predetermined sorts and general syntactic form:
        \\Sigma, D_{ap}, D_{ss}, D_{una}, D_{S_0} """
    def __init__(self, name):
        Theory.__init__(self, name, sorts=["action", "situation"], subsets=["S_0", "ss", "ap"]) # una and \Sigma are standard
        self.actions = [] # keeps track of all action symbols included in the theory

    def get_apa_by_poss(self, poss_atom):
        if not isinstance(poss_atom, PossAtom):
            raise TypeError(f"{poss_atom.tex()} is not a proper PossAtom!")
        for apa in self.axioms["ap"]:
            if poss_atom.action_term.symbol == apa.action:
                return apa
        return None # maybe warrants raising an exception? Fail loudly, after all.

    def instantiate_ap_rhs(self, poss_atom):
        """ Find and instantiate wrt poss_atom the RHS of the matching APA"""
        return self.get_apa_by_poss(poss_atom).instantiate_rhs(poss_atom)

    def is_regressable_to(self, w, rootsit):
        """ Returns true iff formula is regressable to rootsit as per defn. 10 in thesis:
            1. each sit term in formula has form do([a1, ..., an], rootsit)
            2. for each Poss(a, s), a is a term built from an action symbol (not a variable)
            3. no equality or order on situations (prohibited by design, see class EqAtom)
        """
        # Each term is a known number of actions away in the future from sitterm
        for sigma in w.terms(sort="situation"):
            # skip = True # skip if sigma is a sub-situation and not a stand-alone argument of an atom
            # for atom in w.atoms():
            #     if sigma in atom.args:
            #         skip = False
            # if skip:
            #     continue

            s = sigma
            prev = s.previous_sit()
            while True:
                if s == rootsit: # Found root
                    break # regressable by point 1, continue onto point 2
                elif prev is not None: # didn't find root, but can go further back
                    s = prev # get previous situation
                    prev = s.previous_sit()
                else: # All out of ideas
                    return False

        # Each poss atom (if any) has a non-variable action
        for atom in w.atoms():
            if isinstance(atom, PossAtom):
                if atom.action_term.is_var or not atom.action_term.symbol in self.actions: # first arg is variable or some unknown thing
                    return False

        return True # If reached this point, all checks are passed

    def add_axiom(self, formula, force=False, where="default"):
        raise Exception("Don't do this. Use specialized methods.")

    def add_init_axiom(self, axiom, force=False):
        # check if it's a sentence uniform in S_0
        # need formula.terms() generator to get all situations to test
        if not isinstance(axiom, InitAxiom):
            raise Exception("Not a proper init axiom, cannot add to theory")
        self.axioms["S_0"].add(axiom)

    def add_ap_axiom(self, axiom, force=False):
        """
            APA define the actions of the theory. Upon adding an APA, also take an internal note of the action name.
        """
        if not isinstance(axiom, APA):
            raise Exception("Not a proper APA, cannot add to theory")
        elif axiom.action in self.actions:
            raise Exception(f"There already is an action precondition axiom for action {axiom.action}")
        else:
            self.axioms["ap"].add(axiom)
            self.actions.append(axiom.action)


    def add_ss_axiom(self, formula, force=False):
        if (isinstance(formula, RelSSA) or isinstance(formula, FuncSSA)):
            self.axioms["ss"].add(formula)
        else:
            raise Exception("Not a proper SSA, cannot add to theory")

    def rho(self, w, sitterm):
        """ Safe regression: check for regressability first """
        if not self.is_regressable_to(w, sitterm):
           raise Exception(f"Formula {w.tex()} is not regressable to {sitterm}")
        return self._rho(w, sitterm)

    def _rho(self, w, sitterm, depth=0):
        """ Implements \\rho_{sitterm}[formula], the Partial Regression Operator from Definition 11.
            In:
              w: a sitcalc formula (hopefully regressable to sitterm (Defn. 10), will check in code)
              sitterm: a situation term, no other constraints
            Out:
              a new formula, which is the result of regressing given formula bacwards to sitterm using the SSA and APA owned by self.
        """
        prefix = "  "*depth
        print(f"{prefix}Regressing {w.tex()} to term {sitterm.tex()}")
        if isinstance(w, Neg):
            print(f"{prefix}Negation, going in...")
            return Neg(self._rho(w.formula, sitterm, depth=depth+1))
        elif isinstance(w, Junction):
            print(f"{prefix}Junction, going in...")
            return w.__class__(*[self._rho(f, sitterm, depth=depth+1) for f in w.formulas])
        elif isinstance(w, Quantified):
            print(f"{prefix}Quantified, going in...")
            return w.__class__(self._rho(w.formula, sitterm, depth=depth+1))
        else: # Some sort of an atom
            print(f"{prefix}Some sort of an atom...")
            if isinstance(w, PossAtom):  # More stringent checks are in is_regressable
                print(f"{prefix}Poss atom! Replacing by rhs!")
                # instantiate rhs of APA wrt to atom's args, regress that
                return self._rho(self.instantiate_ap_rhs(w), sitterm, depth=depth+1)
            elif w.uniform_in(sitterm): # Uniform in sitterm
                print(f"{prefix}Uniform in {sitterm}, end of branch.")
                return w # Terminal clause
            elif False: # Has a prime func. fluent
                print(f"{prefix}Func. fluents not implemented")
                pass # use func. SSA
            elif False: # Relational fluent atom
                print(f"{prefix}Rel. fluents not implemented")
                pass # use rel. SSA
            else:
                raise Exception(f"Formula {w} is not regressable to {sitterm}!!")

    def describe(self):
        print()
        print("*"*20)
        print(Style.BRIGHT + Fore.YELLOW + f"* Theory {self.name}" + Style.RESET_ALL)
        print("* Sorts:", self.sorts)
        print("* Vocabulary:")
        for _, s in self.vocabulary.items():
            print(f"*   {s}")
        print("* Actions:")
        for a in self.actions:
            print(f"*   {a}")
        print("* Axioms:")
        for ss, st in self.axioms.items():
            print(f"*   {ss} ({len(st)}):")
            for a in st:
                print(f"*     $ {a.formula.tex()} $")

class HybridTheory(BasicActionTheory):
    """ Adds new axiom class: D_{sea} """
    def __init__(self, name):
        Theory.__init__(self, name)


Sitcalc.__populate__()
