import unittest
from theory import *
from formula import *

class FormulaBuilding(unittest.TestCase):
    # self.assertTrue(...)
    # self.assertFalse(...)
    # self.assertEqual(..., ...)
    # with self.assertRaises(Exception): ...

    def test_symbol_creation(self):
        print("\n===== TEST SYMBOL CREATION ======")
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
        print("\n===== TEST FORMULA CREATION ======")
        theory = Theory("test")
        sym_P = Symbol("P", sorts=["object", "time", "situation"])
        sym_Q = Symbol("Q", sorts=["time", "situation"])
        sym_x = Symbol("x", sort="object", is_var=True)
        sym_c = Symbol("c", sort="object")
        sym_t = Symbol("t", sort="time", is_var=True)
        sym_s = Symbol("s", sort="situation", is_var=True)

        sym_y = Symbol("y", sort="object", is_var=True)
        sym_f = Symbol("f", sort="object", sorts=["object", "situation"])
        sym_g = Symbol("g", sort="object", sorts=["time"])

        term_y = Term(sym_y)
        term_f_x_s = Term(sym_f, Term(sym_x), Term(sym_s))
        term_g = Term(sym_g, Term(sym_t))
        print("SUBSTITUTION")
        print(term_f_x_s.tex())
        term_f_x_s.replace_term(Term(sym_x), term_y)
        print(term_f_x_s.tex())
        term_f_x_s.replace_term(Term(sym_y), term_g)
        print(term_f_x_s.tex())

        with self.assertRaises(TypeError):
            term_f_x_s.replace_term(Term(sym_s), term_g)
            print(term_f_x_s.tex())

        term_x = Term(sym_x)
        #print(term_x.tex())

        term_c = Term(sym_c)

        term_t = Term(sym_t)
        #print(term_t.tex())

        term_s = Term(sym_s)
        #print(term_s.tex())

        a1 = Atom(sym_P, term_x, term_t, term_s)
        #print("Atom:", a1.tex())

        with self.assertRaises(TypeError):
            e1 = EqAtom(term_t, term_s)


        e2 = EqAtom(term_t, term_t)
        #print("Equality e2:", e2.tex())

        with self.assertRaises(TypeError):
            e3 = EqAtom(term_t, sym_P)

        with self.assertRaises(TypeError):
            e4 = EqAtom(a1, e2)
            #print("Equality e4:", e4.tex())

        e5 = EqAtom(term_x, term_c)
        #print("Equality e5:", e5.tex())

        sym_S_0 = Symbol("S_0", sort="situation")
        #print(str(sym_S_0))
        term_S_0 = Term(sym_S_0)

        a2 = Atom(sym_P, term_x, term_t, term_S_0)
        #print(a2.tex())

        # Negation

        f1 = Neg(a2)
        #print(f1.tex())

        a3 = Atom(sym_Q, term_t, term_s)
        f2 = And(f1, a3)
        #print("Binary conjunction:", f2.tex(), " instance ", f2)

        f3 = Neg(f2)
        #f3.describe()

        f2 = And(f1)
        #print("Unary conjunction:", f2.tex(), " instance ", f2)
        #f2.describe()

        f2 = And()
        #print("0-ary conjunction:", f2.tex(), " instance ", f2)
        #f2.describe()

        # Quantification - resume after tested simpler formulas

        with self.assertRaises(Exception):
            f1 = Forall(term_S_0, a2)

        f1 = And(Forall(term_t, a2), e2)
        #f1.describe()

        with self.assertRaises(Exception):
            f1 = Forall(term_t, f1)

        f1 = And(Exists(term_s, f1), e5)
        #print("*** ")
        #f1.describe()

        sym_y = Symbol("y", sort="object", is_var=True)

        f4 = Forall(Term(sym_y), f2)
        #f4.describe()

        f5 = Forall(term_x, Forall(term_t, Forall(term_s, f4)))
        #f5.describe()

        # Let's create a successor state axoim!
        # Relational:
        # ()\forall x, a, s) F(x, do(a,s)) \liff \gamma^+(x, a, s) \lor (F(x,s) \land \neg \gamma^-(x,a,s))





    def test_theory(self):
        print("\n===== TEST THEORY CREATION ======")
        theory = Theory("test", sorts=["action", "situation"])

        sym_x = Symbol("x", sort="object", is_var=True)
        sym_a = Symbol("a", sort="action", is_var=True)
        sym_s = Symbol("s", sort="situation", is_var=True)
        sym_F = Symbol("F", sorts=["object", "situation"])
        sym_do = Symbol("do", sort="situation", sorts=["action", "situation"])
        sym_gammaP = Symbol("\\gamma^+", sorts=["object", "action", "situation"])
        sym_gammaN = Symbol("\\gamma^-", sorts=["object", "action", "situation"])

        lhs = Atom(sym_F, Term(sym_x), Term(sym_do, Term(sym_a), Term(sym_s)))

        effect = Atom(sym_gammaP, Term(sym_x), Term(sym_a), Term(sym_s))
        frame = And(Atom(sym_F, Term(sym_x), Term(sym_s)), Neg(Atom(sym_gammaN, Term(sym_x), Term(sym_a), Term(sym_s))))
        rhs = Or(effect, frame)

        iff = Iff(lhs, rhs)
        ssa = Forall(Term(sym_x), Forall(Term(sym_a), Forall(Term(sym_s), iff)))
        #ssa.describe()

        #theory.print_vocabulary()

        with self.assertRaises(Exception): # because ssa contains new symbols
            theory.add_axiom(ssa)

        with self.assertRaises(Exception):
            theory.add_axiom(iff, force=True) # because iff is an open formula

        theory.add_axiom(ssa, force=True)

        with self.assertRaises(Exception): # cannot add same axiom twice
            theory.add_axiom(ssa, force=True)

        #theory.print_vocabulary()

    def test_BAT(self):
        print("\n===== TEST BAT CREATION ======")
        myBAT = BasicActionTheory("Dear Little BAT")
        myBAT.print_vocabulary()

        myF = RelFluentSymbol("MyFluent", sorts=["object", "object"])
        my_x = Term(Symbol("x", sort="object", is_var=True))
        my_y = Term(Symbol("y", sort="object", is_var=True))
        my_z = Term(Symbol("z", sort="object", is_var=True))
        myssa = RelSSA(myF, [my_x, my_y], voc=myBAT.vocabulary)

        print("No effects, only frame:")
        myssa.describe()

        print("Adding a positive effect:")
        a1_sym = Symbol("sleep", sort="action", sorts=["object"])
        cat_sym = Symbol("cat", sort="object", is_var=True)
        fat_sym = Symbol("Fat", sorts=["object"])
        a1 = Term(a1_sym, Term(cat_sym))
        cc1 = Atom(fat_sym, Term(cat_sym))

        with self.assertRaises(Exception):
            myssa.add_pos_effect(a1, cc1)

        cat_sym = Symbol("cat", sort="object")
        a1 = Term(a1_sym, Term(cat_sym))
        cc1 = Atom(fat_sym, Term(cat_sym))
        myssa.add_pos_effect(a1, cc1)
        myssa.describe()

        print("Adding a negative effect:")
        a2_s = Symbol("move", sort="action", sorts=["object", "object"])
        myssa.add_neg_effect(Term(a2_s, my_y, my_z), Tautology())
        myssa.describe()

        print("Adding another negative effect:")
        a3_s = Symbol("eat", sort="action", sorts=["object"])
        myssa.add_neg_effect(Term(a3_s, my_y), Atom(Symbol("Day")))
        myssa.describe()

        print("Test substitutions:")
        with self.assertRaises(Exception):
            myssa.replace_term(my_x, my_z)

        my_c = Term(Symbol("c", sort="object"))
        f = myssa.formula
        print("Before:")
        f.describe()
        f.replace_term(my_x, my_c)
        print("After:")
        f.describe()

        print("\n Test FUNCTIONAL SSA")
        height = FuncFluentSymbol("height", sorts=["object"])
        my_y_reals = Term(Symbol("y", sort="reals", is_var=True))
        with self.assertRaises(Exception):
            myfssa2 = FuncSSA(height, obj_vars=[my_y], voc=myBAT.vocabulary) # Should throw an exception TODO
        myfssa = FuncSSA(height, obj_vars=[my_x], voc=myBAT.vocabulary)
        myfssa.describe()



if __name__ == '__main__':
    unittest.main()
