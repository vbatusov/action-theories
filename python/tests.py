import unittest
from symbol import Symbol
from theory import *
from formula import *

class FormulaBuilding(unittest.TestCase):
    # self.assertTrue(...)
    # self.assertFalse(...)
    # self.assertEqual(..., ...)
    # with self.assertRaises(Exception): ...

    def test_symbol_creation(self):
        # Object constant
        theory = Theory("test")

        theory.add_symbol(Symbol("x", sort="object", is_var=True))

        with self.assertRaises(Exception):
            theory.add_symbol(Symbol("cat", sort="feline")) # bad sort

        theory.add_sort("feline")
        with self.assertRaises(Exception):
            theory.add_sort("feline")

        theory.add_symbol(Symbol("cat", sort="feline"))

    def test_formula_creation(self):
        theory = Theory("test")
        sym_P = Symbol("P", sorts=["object", "time", "situation"])
        sym_Q = Symbol("Q", sorts=["time", "situation"])
        sym_x = Symbol("x", sort="object", is_var=True)
        sym_t = Symbol("t", sort="time", is_var=True)
        sym_s = Symbol("s", sort="situation", is_var=True)

        term_x = Term(sym_x)
        print(term_x.tex())

        term_t = Term(sym_t)
        print(term_t.tex())

        term_s = Term(sym_s)
        print(term_s.tex())

        a1 = Atom(sym_P, term_x, term_t, term_s)
        print(a1.tex())

        sym_S_0 = Symbol("S_0", sort="situation")
        print(str(sym_S_0))
        term_S_0 = Term(sym_S_0)

        a2 = Atom(sym_P, term_x, term_t, term_S_0)
        print(a2.tex())

        # Negation

        f1 = Neg(a2)
        print(f1.tex())

        a3 = Atom(sym_Q, term_t, term_s)
        f2 = And(f1, a3)
        print(f2.tex())

        f3 = Neg(f2)
        self.display(f3)

        # Quantification - resume after tested simpler formulas

        with self.assertRaises(Exception):
            f1 = Forall(term_S_0, a2)

        f1 = Forall(term_t, a2)
        self.display(f1)

        with self.assertRaises(Exception):
            f1 = Forall(term_t, f1)

        f1 = Exists(term_s, f1)
        self.display(f1)

        sym_y = Symbol("y", sort="object", is_var=True)

        f4 = Forall(Term(sym_y), f2)
        self.display(f4)

        f5 = Forall(term_x, Forall(term_t, Forall(term_s, f4)))
        self.display(f5)


    def display(self, formula):
        print("-----formula {}-----".format(formula.tex()))
        #print("  Symbols in  {}".format(formula.tex()))
        #for sym in formula.iter_symbols():
        #    print("    {}".format(str(sym)))

        #print("  Structs in  {}".format(formula.tex()))
        #for struct in formula.iter_structs():
        #    print("    {}".format(struct.tex()))

        print("  All variables:")
        for v in formula.vars():
            print("  {}".format(v.tex()))

        print("  Non-free variables:")
        for v in formula.nonfree_vars():
            print("  {}".format(v.tex()))

        print("  Free variables:")
        for v in formula.free_vars():
            print("  {}".format(v.tex()))

if __name__ == '__main__':
    unittest.main()



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
# theory = Theory("test")
#
#
# h = Symbol("h", sorts=["object", "time", "situation"], sort="reals") # Inferred to be a temp fluent
# c = Symbol("C", sorts=["object", "situation"]) # Context predicate
# p = Symbol("P", sorts=["object"])
# x = Symbol("x", sort="object", is_var=True)
# do = Symbol("do", sorts=["action","situation"], sort="situation")
# s_0 = Symbol("S_0", sort="situation")
# a_noop = Symbol("sleep", sorts=["time"], sort="action")
# tau = Symbol("\\tau", sort="time")
# sigma = Symbol("\\sigma", sort="situation")
# s = Symbol("s", sort="situation", is_var=True)
#
#
# theory.add_symbol(h)
# theory.add_symbol(c)
# theory.add_symbol(x)
# theory.add_symbol(p)
#
# theory.print_vocabulary()
#
# sitterm = Term(do, Term(a_noop, Term(tau)), Term(s_0))
# term = Term(h, Term(x), Term(tau), sitterm)
# print("h(x,\\tau, do(sleep(\\tau), S_0)) -> ", term.tex())
#
# c_atom = Atom(c, Term(x), sitterm)
# print("C(x, ...) -> ", c_atom.tex(), ", has free x: ", c_atom.has_free(Term(x)))
#
# allxc = Forall(Term(x), c_atom)
# print("\\forall x (C(...)) -> ", allxc.tex(), ", has free x: ", allxc.has_free(Term(x)), ", has free s: ", c_atom.has_free(Term(s)))
#
# AsExC = Forall(Term(x), Exists(Term(s), Neg(Atom(c, Term(x), Term(s)))))
# print("\\forall x \\exists s (C(x,s)) -> ", AsExC.tex(), ", has free x: ", AsExC.has_free(Term(x)), ", has free s: ", AsExC.has_free(Term(s)))
#
# disj = Or(Atom(p, Term(x)), Neg(Exists(Term(x), Atom(c, Term(x), Term(s)))))
# print(str(disj))
# print("P(x) \\lor \\neg (C(x,s)) -> ", disj.tex(), ", has free x: ", disj.has_free(Term(x)), ", has free s: ", disj.has_free(Term(s)))
#
# print("\nSymbols in disj:")
# for s in disj.iter_symbols():
#     print("  ", str(s))
# # # Build the formula:
#
# # y = Var("y", sort="reals")
# # t = Var("t", sort="time")
# # s = Var("s", sort="situation")
# # lhs = Equals(Term(h, [x, t, s]), y)
# # tca1 = And(Atom(c, [x, s]), Equals(y, tca1math))
# # tca2 = And(Not(Atom(c, [x,s ])), Equals(y, tca2math))
# # rhs = Or(tca1, tca2)
# # iff = Iff(lhs, rhs)
# # sea = Forall(x, Forall(y, Forall(t, Forall(s, iff))))
#
#
# # for s in [h, c, x]:
# #     print(str(s), repr(s))
