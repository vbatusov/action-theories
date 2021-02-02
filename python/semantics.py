from fol import *
from sitcalc import *
import pyswip
from tabulate import tabulate

class Semantics(object):
    """ Gets a sit. calc. initial theory, converts to Prolog clauses (if possible),
        Answers queries about KB.
    """
    def __init__(self, bat):
        """ Convert theory to Prolog clauses (if Horn)
            init_theory is BasicActionTheory.axioms["S_0"]
        """
        #self.symbol_map = {} # From
        print("*"*65)
        print("Please verify the resulting clauses against the initial theory!")
        print("This semantics is experimental and incomplete!")
        print("REMEMBER: Domain Closure and Negation as Failure are in effect!\n")
        self._bat = bat # for reference
        self._translation = [] # Just a _translation table from TeX to Prolog for display purposes
        self._kb = self._create_kb(bat)
        print(tabulate(self._translation, headers=["Supplied axiom", "Generated prolog clause"]))
        print()
        print("*"*65)

    def _create_kb(self, bat):
        kb = pyswip.Prolog()
        for axiom in bat.axioms["S_0"]:
            self._add_axiom(bat, axiom, kb)
        return kb


    def _add_axiom(self, bat, axiom, kb):
        formula = bat.suppress_s(axiom.formula)
        if len(tuple(formula.vars())) > 0:
            raise Exception("Can't process formulas with variables!")

        #print(f"\nLooking at axiom: {formula.tex()}")
        # For now, assume all axioms are atoms (possibly equality atoms)
        if isinstance(formula, EqAtom):
            #print("Equality atom")
            (lhs, rhs) = formula.args
            if isinstance(lhs, UConst) and isinstance(rhs, UConst):
                raise Exception(f"Can't equate two distinct constants {lhs.tex()} and {rhs.tex()}")
            elif not isinstance(lhs, UConst) and not isinstance(rhs, UConst):
                raise Exception(f"Can't equate two non-constant terms {lhs.tex()} and {rhs.tex()}")

            #print(f"  Translates to {translate_eq(lhs, rhs)}")
            rule = translate_equality(lhs, rhs)
            kb.assertz(rule)
            self._translation.append([axiom.formula.tex(), rule])

        elif isinstance(formula, Atom):
            #print(f"  Translates to {translate_atom(formula)}")
            rule = translate_atom(formula)
            kb.assertz(rule)
            self._translation.append([axiom.formula.tex(), rule])

        elif isinstance(formula, Neg):
            self._translation.append([axiom.formula.tex(), "-"])
        elif isinstance(formula, Junction):
            self._translation.append([axiom.formula.tex(), "-"])
        else:
            raise Exception(f"Unrecognized formula {axiom.formula.tex()} ({axiom.formula.__class__})")


    def _swi_eval(self, prolog_query):
        """ Use SLDNF-resolution to prove query from KB
            Empty tuple return means query cannot be proved """
        print(f"Posing query {prolog_query}")
        return (tuple(self._kb.query(prolog_query, catcherrors=False)) != ())

    # Specific FOL-invoked eval methods (standard public interface)
    def eval_query(self, query):
        """ Evaluate the query against the KB. Requires converting to Prolog goals (if even possible)
            This is a catch-all method, which must dispatch based on incoming type """
        if not query.is_sentence():
            raise Exception("Cannot have free variables in a query yet.")
        elif not query.uniform_in(TERM["S_0"]):
            raise Exception("Cannot answer queries about situations other than S_0! Regress first.")

        if isinstance(query, Atom): # Base case for recursion
            return self.eval_atomic(query)
        else: # for non-atomic formulas, delegate to their own eval. This is the recursive case
            return query.eval(self) # will call this same method, but wrt to a buch of other formulas

    def eval_atomic(self, atomic):
        if isinstance(atomic, EqAtom): # An equality atom, possibly involvling a fluent
            print(f"Evaluating equality atom {atomic.tex()}")
            return self.eval_equality(atomic)
        # elif isinstance(atomic, RelFluent): # Relational fluent atom
        #     print(f"Evaluating equality atom {atomic.tex()}")
        #     return self.eval_relational_fluent(atomic)
        else: # Generic atom
            print(f"Evaluating regular atom {atomic.tex()}")
            return self.eval_atom(atomic)

    def eval_atom(self, atom):
        """ Any FOL atom not covered by EqAtom or RelFluent """
        return self._swi_eval(translate_atom(atom))

    def eval_equality(self, eq):
        """ atom is EqAtom """
        return self._swi_eval(translate_equality(eq.args[0], eq.args[1]))


    def eval_forall(self, universal):
        """ A universally-quantified formula
            substitute every constant in place of var, make a conjunction, evaluate as usual
        """
        pass

    def eval_exists(self, existential):
        """ An existentially-quantified formula
            substitute every constant in place of var, make a disjunction, evaluate as usual
        """
        print(f"Evaluating existential {existential.tex()}")
        # Get a new Prolog var, remove existential, insert new var where existential one used to be

        # As a shortcut, seeing as keeping track of variables is difficult, let's use known constants
        # This is a temporary solution and might not be a good one
        # We'll see
        print(f"Sort of var: {existential.var.sort}")
        # Get all constants of the right sort
        fol_constants = set(c for c in self._bat.constants[existential.var.sort])
        print(f"Original names: {[c.name for c in fol_constants]}")
        #swi_constants = [f"c_{c}" for c in fol_constants]
        #print(f"Prolog names: {swi_constants}")
        for const in fol_constants:
            term = Term(const)
            new_e = copy.deepcopy(existential.formula)
            new_e.replace_term(existential.var, term)
            print(f"  Will try {new_e.tex()}")
            if self.eval_query(new_e):
                print(f"   -> Yes!!!")
                return True
            else:
                print(f"   -> Sorry...")
        return False




def translate_equality(lhs, rhs):
    """ This function is shared between init axioms and queries, be careful """
    print(f"Translating equality {lhs.tex()} = {rhs.tex()}")
    if lhs.is_atomic() and rhs.is_atomic():
        return f"{translate_term(lhs)}={translate_term(rhs)}"

    outer, inner = "", ""
    if lhs.is_atomic():
        (lhs, rhs) = (rhs, lhs)
    # now rhs is atomic
    args = translate_term_args(lhs) + (translate_term(rhs),) # Magic trick, turns function into predicate
    result = combine_name_args(translate_term_name(lhs), args)
    print(f"Result: {result}")
    return result

def translate_term_name(term):
    prefix = "f_"
    if len(term.args) == 0:
        prefix = "c_"
    return f"{prefix}{term.symbol.name}"

def translate_term_args(term): # returns a tuple of args
    return tuple(translate_term(a) for a in term.args if a.sort != "situation")

def translate_atom_args(term, fluent=False): # returns a tuple of args

    # !!!!!
    # THis is incomplete! What if atom has non-constant arguments???
    if fluent:
        return tuple(translate_term(a) for a in term.args[:-1])
    else:
        return tuple(translate_term(a) for a in term.args)

def translate_term(term):
    return combine_name_args(translate_term_name(term), translate_term_args(term))

def combine_name_args(name, args):
    if len(args) > 0:
        return "{}({})".format(name, ",".join(args))
    return name

def translate_atom_name(atom):
    return f"p_{atom.symbol.name}"

def translate_atom(atom):
    name = translate_atom_name(atom)
    args = translate_atom_args(atom)
    return combine_name_args(name, args)
