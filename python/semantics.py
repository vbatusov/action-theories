from fol import *
from sitcalc import *
import pyswip

class Semantics(object):
    """ Gets a sit. calc. initial theory, converts to Prolog clauses (if possible),
        Answers queries about KB.
    """
    def __init__(self, init_theory):
        """ Convert theory to Prolog clauses (if Horn)
            init_theory is BasicActionTheory.axioms["S_0"]
        """
        #self.symbol_map = {} # From
        print("Please verify the resulting clauses against the initial theory!")
        print("This semantics is experimental and incomplete!")
        self.kb = self.create_kb(init_theory)

    def create_kb(self, init_theory):
        kb = pyswip.Prolog()
        for axiom in init_theory:
            self.add_axiom(axiom, kb)
        return kb


    def add_axiom(self, axiom, kb):
        formula = axiom.formula
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
            kb.assertz(translate_eq(lhs, rhs))

        elif isinstance(formula, Atom):
            #print(f"  Translates to {translate_atom(formula)}")
            kb.assertz(translate_atom(formula))

        elif isinstance(formula, Neg):
            pass #print("Skipping negation! Relying on Negation As Failure.")
        elif isinstance(formula, Junction):
            pass #print("Non-atomic formulas not implemented!")
        else:
            raise Exception(f"Unrecognized formula {formula.tex()} ({formula.__class__})")

    def convert_query(self, formula):
        """ Only atoms and equalities for now """
        if isinstance(formula, EqAtom):
            #print("Equality atom")
            (lhs, rhs) = formula.args
            if isinstance(lhs, UConst) and isinstance(rhs, UConst):
                raise Exception(f"Can't equate two distinct constants {lhs.tex()} and {rhs.tex()}")
            elif not isinstance(lhs, UConst) and not isinstance(rhs, UConst):
                raise Exception(f"Can't equate two non-constant terms {lhs.tex()} and {rhs.tex()}")

            #print(f"  Translates to {translate_eq(lhs, rhs)}")
            return translate_eq(lhs, rhs)

        elif isinstance(formula, Atom):
            #print(f"  Translates to {translate_atom(formula)}")
            return translate_atom(formula)

        elif isinstance(formula, Neg):
            pass #print("Skipping negation! Relying on Negation As Failure.")
        elif isinstance(formula, Junction):
            pass #print("Non-atomic formulas not implemented!")
        else:
            raise Exception(f"Unrecognized formula {formula.tex()} ({formula.__class__})")


    def eval(self, query):
        """ Evaluate the query against the KB. Requires converting to Prolog goals (if even possible) """
        if self.kb is None:
            raise Exception("No Knowledge Base yet!")
        goal = self.convert_query(query)
        ans = self.kb.query(goal, catcherrors=False)
        return (tuple(ans) != ())

def translate_eq(lhs, rhs):
    outer, inner = "", ""
    if isinstance(lhs, UConst):
        (lhs, rhs) = (rhs, lhs)
    # now rhs is the constant
    args = translate_term_args(lhs) + (translate_term(rhs),)
    return combine_name_args(translate_term_name(lhs), args)

def translate_term_name(term):
    prefix = "f_"
    if len(term.args) == 0:
        prefix = "c_"
    return f"{prefix}{term.symbol.name}"

def translate_term_args(term): # returns a tuple of args
    return tuple(translate_term(a) for a in term.args if a.sort != "situation")

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
    args = translate_term_args(atom) # should work for atoms, too
    return combine_name_args(name, args)
