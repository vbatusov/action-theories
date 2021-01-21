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

    def test_substitution(self):
        x = Term(Symbol("x", sort="object", is_var=True))
        y = Term(Symbol("y", sort="object", is_var=True))
        atom1 = Atom(Symbol("P", sorts=["object"]), x)
        atom2 = copy.deepcopy(atom1)
        print("atom1 before:", atom1.tex())
        print("atom2 before:", atom2.tex())
        atom2.replace_term(x,y)
        print("atom1 after:", atom1.tex())
        print("atom2 after:", atom2.tex())

    def test_BAT(self):
        print("\n===== TEST BAT CREATION ======")
        myBAT = BasicActionTheory("Dear Little BAT")
        myBAT.print_vocabulary()

        print("\n--- Relational SSA ---")
        myF = RelFluentSymbol("MyFluent", sorts=["object", "object"])
        my_x = Term(Symbol("x", sort="object", is_var=True))
        my_y = Term(Symbol("y", sort="object", is_var=True))
        my_z = Term(Symbol("z", sort="object", is_var=True))
        myssa = RelSSA(myF, [my_x, my_y])

        print("\nNo effects, only frame:")
        myssa.describe()

        print("\nAdding a positive effect:")
        a1_sym = Symbol("sleep", sort="action", sorts=["object"])
        cat_sym = Symbol("cat", sort="object", is_var=True)
        fat_sym = Symbol("Fat", sorts=["object"])
        a1 = Term(a1_sym, Term(cat_sym))
        cc1 = Atom(fat_sym, Term(cat_sym))

        # Don't remember what this is testing, but this stopped being raised
        # After I stopped free variable generator from returning duplicates
        #with self.assertRaises(Exception):
        #    myssa.add_pos_effect(a1, cc1)

        cat_sym = Symbol("cat", sort="object")
        a1 = Term(a1_sym, Term(cat_sym))
        cc1 = Atom(fat_sym, Term(cat_sym))
        myssa.add_pos_effect(a1, cc1)
        myssa.describe()

        print("\nAdding a negative effect:")
        a2_s = Symbol("move", sort="action", sorts=["object", "object"])
        myssa.add_neg_effect(Term(a2_s, my_y, my_z), Tautology())
        myssa.describe()

        print("\nAdding another negative effect:")
        a3_s = Symbol("eat", sort="action", sorts=["object"])
        myssa.add_neg_effect(Term(a3_s, my_y), Atom(Symbol("Day")))
        myssa.describe()

        print("\nTest substitutions:")
        with self.assertRaises(Exception):
            myssa.replace_term(my_x, my_z)

        print("(Replace variable x by constant c)")
        my_c = Term(Symbol("c", sort="object"))
        f = myssa.formula
        print("Before:")
        f.describe()
        f.replace_term(my_x, my_c)
        print("After:")
        f.describe()

        print("\n--- Functional SSA ---")
        height = FuncFluentSymbol("height", sorts=["object"])
        my_y_reals = Term(Symbol("y", sort="reals", is_var=True))
        with self.assertRaises(Exception):
            myfssa2 = FuncSSA(height, obj_vars=[my_y]) # Should throw an exception TODO
        myfssa = FuncSSA(height, obj_vars=[my_x])
        myfssa.describe()

        print("\nAdding an effect")
        a1_sym = Symbol("eat\\_mushroom", sort="action", sorts=["object"])
        m = Term(Symbol("x_1", sort="object", is_var=True))
        a1 = Term(a1_sym, m)
        NP_sym = Symbol("NotPoison", sorts=["object"])
        GF_sym = Symbol("GrowthFactor", sorts=["object", "reals"])
        NP = Atom(NP_sym, m)
        GF = Atom(GF_sym, m, my_y_reals)
        #func = EqAtom() # need arithmetic for this
        # y = height(s) * growth_factor
        myfssa.add_effect(a1, And(NP, GF))
        myfssa.describe()

        sup = myfssa.formula.open()
        print("Suppressed: ")
        sup.describe()

        print("\nAdding a second effect")
        # a = think(d, t) \land y = height(d, s) + 2*t
        a2_sym = Symbol("think", sort="action", sorts=["object", "reals"])
        t = Term(Symbol("t", sort="reals", is_var=True))
        d = Term(Symbol("d", sort="object"))
        two = Term(Symbol("2", sort="reals"))
        mult = Term(myBAT.vocabulary["*"], two, t)
        ht = Term(height, d, myBAT.special_terms["s"])
        sm = Term(myBAT.vocabulary["+"], ht, mult)
        ee = EqAtom(my_y_reals, sm)
        a2 = Term(a2_sym, d, t)
        myfssa.add_effect(a2, ee)
        myfssa.describe()

        sup = myfssa.formula.open()
        print("Suppressed: ")
        sup.describe()

        # Now, let's practice adding SSA to a BAT
        print("\nAdding SSA to BAT...")
        myBAT.add_ss_axiom(myssa)
        myBAT.add_ss_axiom(myfssa)

        myBAT.describe()


    def test_BW(self):
        # Create a basic action theory
        bat = BasicActionTheory("Blocks World")
        bat.describe()

        # Create common symbols and terms
        s = bat.special_terms["s"]
        S_0 = bat.special_terms["S_0"]
        move = Symbol("move", sort="action", sorts=["object","object"])
        x = Term(Symbol("x", sort="object", is_var=True))
        y = Term(Symbol("y", sort="object", is_var=True))
        z = Term(Symbol("z", sort="object", is_var=True))
        move_x_y = Term(move, x, y)
        move_y_z = Term(move, y, z)
        move_y_x = Term(move, y, x)

        # Create domain constants
        T = Term(Symbol("T", sort="object"))
        A = Term(Symbol("A", sort="object"))
        B = Term(Symbol("B", sort="object"))
        C = Term(Symbol("C", sort="object"))

        # Create fluent symbols
        on = FuncFluentSymbol("on", sorts=["object"], sort="object")
        clear = RelFluentSymbol("clear", sorts=["object"])

        # Construct subformulas and formulas
        clear_x_s = Atom(clear, x, s)
        neq_x_y = Neg(EqAtom(x, y))
        neq_x_T = Neg(EqAtom(x, T))
        clear_y_s = Atom(clear, y, s)
        eq_y_T = EqAtom(y, T)
        rhs = And(clear_x_s, neq_x_y, neq_x_T, Or(clear_y_s, eq_y_T))

        # Add a precondition axiom
        apa = APA(move_x_y, rhs=rhs)
        bat.add_ap_axiom(apa)
        bat.describe()

        # Create and add initial state axioms
        init1 = InitAxiom(EqAtom(Term(on, A, S_0), T).close())
        init2 = InitAxiom(EqAtom(Term(on, C, S_0), B).close())
        init3 = InitAxiom(EqAtom(Term(on, B, S_0), T).close())
        init4 = InitAxiom(Atom(clear, A, S_0).close())
        init5 = InitAxiom(Atom(clear, C, S_0).close())
        init6 = InitAxiom(Neg(Atom(clear, B, S_0).close()))

        bat.add_init_axiom(init1)
        bat.add_init_axiom(init2)
        bat.add_init_axiom(init3)
        bat.add_init_axiom(init4)
        bat.add_init_axiom(init5)
        bat.add_init_axiom(init6)
        bat.describe()

        # Construct and add SSA for clear (relational)
        ssa_clear = RelSSA(clear, [x])  # Create the frame-only axiom
        ssa_clear.add_pos_effect(move_y_z, context=EqAtom(y, Term(on, x, s))) # Add a positive effect
        ssa_clear.add_neg_effect(move_y_x)
        bat.add_ss_axiom(ssa_clear)
        bat.describe()

        # Construct and add SSA for on (functional)
        ssa_on = FuncSSA(on, [x])
        ssa_on.add_effect(move_x_y)
        bat.add_ss_axiom(ssa_on)
        bat.describe()

        # NExt, add SSA
        # Implement BAT.situations() to iterate through the entire infinite tree of situations
        # Finish regression and test on a ground situation term
        # Semantics
        # At this point, will be able to implement actual cause analysis
        # Extend to hybrid case, with both FO and SO SEA
        # Test on a toy domain with numerical functions (Lotka-Volterra Zayats-Volk)
        # Implement regression for Hybrid
        # Implement causal analysis for hybrid


if __name__ == '__main__':
    unittest.main()
