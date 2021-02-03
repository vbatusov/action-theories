import unittest
from sitcalc import *
from fol import *

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

    # THIS IS ALL OUTDATED DUE TO REFACTORING
    # def test_BAT(self):
    #     print("\n===== TEST BAT CREATION ======")
    #     myBAT = BasicActionTheory("Dear Little BAT")
    #     myBAT.print_vocabulary()
    #
    #     print("\n--- Relational SSA ---")
    #     myF = RelFluentSymbol("MyFluent", sorts=["object", "object"])
    #     my_x = Term(Symbol("x", sort="object", is_var=True))
    #     my_y = Term(Symbol("y", sort="object", is_var=True))
    #     my_z = Term(Symbol("z", sort="object", is_var=True))
    #     #myF2 = RelFluent("MyFluent2", sitterm=vvvv)
    #     myssa = RelSSA(myF, [my_x, my_y])
    #
    #
    #     print("\nNo effects, only frame:")
    #     myssa.describe()
    #
    #     print("\nAdding a positive effect:")
    #     a1_sym = Symbol("sleep", sort="action", sorts=["object"])
    #     cat_sym = Symbol("cat", sort="object", is_var=True)
    #     fat_sym = Symbol("Fat", sorts=["object"])
    #     a1 = Term(a1_sym, Term(cat_sym))
    #     cc1 = Atom(fat_sym, Term(cat_sym))
    #
    #     # Don't remember what this is testing, but this stopped being raised
    #     # After I stopped free variable generator from returning duplicates
    #     #with self.assertRaises(Exception):
    #     #    myssa.add_pos_effect(a1, cc1)
    #
    #     cat_sym = Symbol("cat", sort="object")
    #     a1 = Term(a1_sym, Term(cat_sym))
    #     cc1 = Atom(fat_sym, Term(cat_sym))
    #     myssa.add_pos_effect(a1, cc1)
    #     myssa.describe()
    #
    #     print("\nAdding a negative effect:")
    #     a2_s = Symbol("move", sort="action", sorts=["object", "object"])
    #     myssa.add_neg_effect(Term(a2_s, my_y, my_z), Tautology())
    #     myssa.describe()
    #
    #     print("\nAdding another negative effect:")
    #     a3_s = Symbol("eat", sort="action", sorts=["object"])
    #     myssa.add_neg_effect(Term(a3_s, my_y), Atom(Symbol("Day")))
    #     myssa.describe()
    #
    #     print("\nTest substitutions:")
    #     with self.assertRaises(Exception):
    #         myssa.replace_term(my_x, my_z)
    #
    #     print("(Replace variable x by constant c)")
    #     my_c = Term(Symbol("c", sort="object"))
    #     f = myssa.formula
    #     print("Before:")
    #     f.describe()
    #     f.replace_term(my_x, my_c)
    #     print("After:")
    #     f.describe()
    #
    #     print("\n--- Functional SSA ---")
    #     height = FuncFluentSymbol("height", sorts=["object"])
    #     my_y_reals = Term(Symbol("y", sort="reals", is_var=True))
    #     with self.assertRaises(Exception):
    #         myfssa2 = FuncSSA(height, obj_vars=[my_y]) # Should throw an exception TODO
    #     myfssa = FuncSSA(height, obj_vars=[my_x])
    #     myfssa.describe()
    #
    #     print("\nAdding an effect")
    #     a1_sym = Symbol("eat\\_mushroom", sort="action", sorts=["object"])
    #     m = Term(Symbol("x_1", sort="object", is_var=True))
    #     a1 = Term(a1_sym, m)
    #     NP_sym = Symbol("NotPoison", sorts=["object"])
    #     GF_sym = Symbol("GrowthFactor", sorts=["object", "reals"])
    #     NP = Atom(NP_sym, m)
    #     GF = Atom(GF_sym, m, my_y_reals)
    #     #func = EqAtom() # need arithmetic for this
    #     # y = height(s) * growth_factor
    #     myfssa.add_effect(a1, And(NP, GF))
    #     myfssa.describe()
    #
    #     sup = myfssa.formula.open()
    #     print("Suppressed: ")
    #     sup.describe()
    #
    #     print("\nAdding a second effect")
    #     # a = think(d, t) \land y = height(d, s) + 2*t
    #     a2_sym = Symbol("think", sort="action", sorts=["object", "reals"])
    #     t = Term(Symbol("t", sort="reals", is_var=True))
    #     d = Term(Symbol("d", sort="object"))
    #     two = Term(Symbol("2", sort="reals"))
    #     mult = Term(myBAT.vocabulary["*"], two, t)
    #     ht = Term(height, d, TERM["s"])
    #     sm = Term(myBAT.vocabulary["+"], ht, mult)
    #     ee = EqAtom(my_y_reals, sm)
    #     a2 = Term(a2_sym, d, t)
    #     myfssa.add_effect(a2, ee)
    #     myfssa.describe()
    #
    #     sup = myfssa.formula.open()
    #     print("Suppressed: ")
    #     sup.describe()
    #
    #     # Now, let's practice adding SSA to a BAT
    #     print("\nAdding SSA to BAT...")
    #     myBAT.add_ss_axiom(myssa)
    #     myBAT.add_ss_axiom(myfssa)
    #
    #     myBAT.describe()

    def test_simplification(self):
        S_0 = TERM["S_0"]
        C = UConst("C")
        y = ObjVar("y")
        T = UConst("T")
        z = ObjVar("z")

        print("TEST 1")
        query = Exists(z, Exists(y, And(EqAtom(C, y), EqAtom(T, z), EqAtom(y, ObjFluent("on", C, S_0)))))
        print(f"Query: {query.tex()}")
        print(f"Simpl: {query.simplified().tex()}")

        print("TEST 2")
        y_ = ObjVar("y'")
        B = UConst("B")
        query = And(EqAtom(y, C), Neg(Exists(y_, EqAtom(B, y_))))
        print(f"Query: {query.tex()}")
        print(f"Simpl: {query.simplified().tex()}")

    def test_BW(self):
        import blocksworld as bw

        bw.bat.describe()

        # Test regressability
        #print("\nTest regression")
        w = RelFluent("clear", bw.A, bw.S_0)
        sitterm = bw.S_0
        do_a_s = TERM["do(a,s)"]
        w = RelFluent("clear", bw.A, do_a_s)
        w = PossAtom(TERM["a"], bw.s)
        w = PossAtom(bw.move_x_y, bw.s)

        # Test APA RHS instantiation
        w = PossAtom(ActionTerm("move", bw.A, bw.B), bw.S_0)
        irhs = bw.bat.instantiate_ap_rhs(w)
        print(f"\nInstantiating RHS wrt\n    {w.tex()}\nyields\n    {irhs.tex()}")
        w = PossAtom(ActionTerm("move", bw.A, bw.B), do_a_s)
        irhs = bw.bat.instantiate_ap_rhs(w)
        print(f"\nInstantiating RHS wrt\n    {w.tex()}\nyields\n    {irhs.tex()}")
        w = PossAtom(bw.noop, do_a_s)
        print(f"\nInstantiating RHS wrt\n    {w.tex()}\nyields\n    {bw.bat.instantiate_ap_rhs(w).tex()}")

        # Test substitution
        print("\nTest of general substitutions")
        # A(y,x) [x/f(y), y/x] => A(x,f(y))
        f_sym = Symbol("f", sort="object", sorts=["object"])
        f_y = Term(f_sym, bw.y)
        at = Atom(Symbol("A", sorts=["object", "object"]), bw.y, bw.x)
        src = [bw.x,bw.y]
        tgt = [f_y, bw.x]
        print(f"Source: {at.tex()}")
        srctex = [v.tex() for v in src]
        tgttex = [v.tex() for v in tgt]
        subs = ", ".join([f"{s}/{t}" for (s,t) in zip(srctex, tgttex)])
        print(f"Substitution: ({subs})")
        at2 = at.apply_substitution(src, tgt)
        print(f"Result 1: {at2.tex()}")
        at2 = at2.apply_substitution(src, tgt)
        print(f"Result 2: {at2.tex()}")
        at2 = at2.apply_substitution(src, tgt)
        print(f"Result 3: {at2.tex()}")

        # Test regression
        print(f"\nTesting regression of Poss atoms")
        # APA only
        w = PossAtom(ActionTerm("move", bw.A, bw.B), do_a_s)
        print(f"Is {w.tex()} regressable to {do_a_s.tex()}? -> {bw.bat.is_regressable_to(w, do_a_s)}")
        regr = bw.bat.rho(w, do_a_s)
        print(f"Result: {regr.tex()}")
        # works. Now, implement full regression (add func and rel SSA)

        # Test rel SSA regression
        print(f"\nUsing relational SSA")
        sigma = Do(ActionTerm("move", bw.B, bw.T), TERM["s"]) #SitTerm(SYM["do"], ActionTerm("move", B, T), TERM["s"])
        w = PossAtom(ActionTerm("move", bw.A, bw.B), sigma)
        print(f"Is {w.tex()} regressable to {bw.s.tex()}? -> {bw.bat.is_regressable_to(w, bw.s)}")
        regr = bw.bat.rho(w, bw.s)
        print(f"Result: {regr.tex()}")

        # A simpler case
        print(f"\nUsing relational SSA: Test 2")
        w = RelFluent("clear", bw.C, SitTerm(SYM["do"], ActionTerm("move", bw.B, bw.A), TERM["S_0"]))
        print(f"Is {w.tex()} regressable to {bw.S_0.tex()}? -> {bw.bat.is_regressable_to(w, bw.S_0)}")
        regr = bw.bat.rho(w, bw.S_0)
        print(f"Result: {regr.tex()}")
        regr = regr.simplified()
        print(f"Same, simplified: {regr.tex()}")

        # Test functional fluent regression
        print(f"\nRegression involving functional SSA: Test 1")
        # B = on(A, do(move(C,T), S_0))
        # "B is on A after moving C to table" (false)
        query = EqAtom(bw.B, ObjFluent("on", bw.A, Do(ActionTerm("move", bw.C, bw.T), bw.S_0)))
        print(query.tex())
        print(f"All terms in {regr.tex()}:")
        for t in query.terms():
            if isinstance(t, FuncFluent):
                print(f"  {t.tex()} (FUNCTIONAL FLUENT TERM!!!)")
            else:
                print(f"  {t.tex()} (skip)")


        regr = bw.bat.rho(query, bw.S_0)
        print(f"Result: {regr.tex()}")
        regr = regr.simplified()
        print(f"Same, simplified: {regr.tex()}")

        print(Fore.RED + f"\nLet's now have a regression which involves all cases!" + Style.RESET_ALL)
        sigma_1 = Do(ActionTerm("move", bw.C, bw.T), bw.S_0)
        sigma_2 = Do(ActionTerm("noop"), sigma_1)
        sigma_3 = Do(ActionTerm("move", bw.A, bw.B), sigma_2)
        #sigma_4 = Do(ActionTerm("move", , ), sigma)
        q = []
        q.append(EqAtom(bw.B, ObjFluent("on", bw.A, sigma_3)))
        q.append(PossAtom(ActionTerm("move", bw.A, bw.B), sigma_1))
        q.append(RelFluent("clear", bw.C, sigma_2))
        query = And(*q)
        print("\nQuery:")
        print(f"\nQuery: ${query.tex()}$")
        regr = bw.bat.rho(query, bw.S_0)
        print(f"Result: ${regr.tex()}$")
        print("Simplified stable:")
        simp = regr.simplified_stable()
        print("\\begin{align*}")
        print(f"&{simp.tex()}")
        print("\\end{align*}")

        print()
        print("Separately:")
        for query in q:
            print(f"\nQuery: ${query.tex()}$")
            regr = bw.bat.rho(query, bw.S_0)
            print(f"Result: ${regr.tex()}$")
            print("Simplified stable:")
            simp = regr.simplified_stable()
            print("\\begin{align*}")
            print(f"&{simp.tex()}")
            print("\\end{align*}")

        print(f"Terms in {sigma_3.tex()}")
        for t in sigma_3.terms(sort="situation"):
            print (f"  {t.tex()}")
        print(f"What is {q[0].tex()} regressable to?")
        for sig in [sigma_1, sigma_2, sigma_3, TERM["S_0"], TERM["s"], Do(ActionTerm("noop"),TERM["S_0"])]:
            print(f"{sig.tex()}? -> {bw.bat.is_regressable_to(q[0], sig)}")

    def test_semantics(self):
        import blocksworld as bw
        import semantics

        bw.bat.describe()
        sem = semantics.Semantics(bw.bat)

        q = []
        q.append(EqAtom(ObjFluent("on", bw.B, TERM["S_0"]), ObjFluent("on", bw.A, TERM["S_0"])))

        query = And(*q)

        print("\nFirst query (should be True): 'A and B are on the same thing'")
        answer = bw.bat.entails(query, sem)
        self.assertTrue(answer)
        print(f"{query.tex()} evaluates to {answer}")

        print("\nSecond query (should be False): 'All blocks (which do not denote the table) are on the table'")
        # all blocks (which are not the table) are on table
        x = ObjVar("x")
        query = Forall(x, Implies(Neg(EqAtom(x, bw.T)), EqAtom(ObjFluent("on", x, TERM["S_0"]), bw.T)))
        # f2 = bw.bat.suppress_s(query)
        # f3 = f2.flatten(VarSource())
        answer = bw.bat.entails(query, sem) #sem.eval_query(f3)
        print(f"{query.tex()} evaluates to {answer}")
        self.assertFalse(answer)

        print("\nThird query (should be True): 'All blocks (which do not denote the table) except C are on the table'")
        # all blocks (which are not the table) except C are on table
        query = Forall(x, Implies(Neg(EqAtom(x, bw.T)), Or(EqAtom(x, bw.C), EqAtom(ObjFluent("on", x, TERM["S_0"]), bw.T))))
        # f2 = bw.bat.suppress_s(query)
        # f3 = f2.flatten(VarSource())
        answer = bw.bat.entails(query, sem) #sem.eval_query(f3)
        print(f"{query.tex()} evaluates to {answer}")
        self.assertTrue(answer)

        # Every block which has something on it is not clear
        # Reminder: on(x) = y iff x is on y
        # \forall x (exists z(on(z,s)=x) \to neg clear(x, s))
        print("\nFourth query (should be True): 'Every block which has something on it is not clear'")
        x = ObjVar('x')
        z = ObjVar('z')
        s = TERM['S_0']
        query = Forall(x, Implies(Exists(z, EqAtom(ObjFluent("on", z, s), x)), Neg(RelFluent("clear", x, s))))
        # f2 = bw.bat.suppress_s(query)
        # f3 = f2.flatten(VarSource())
        answer = bw.bat.entails(query, sem) #sem.eval_query(f3)
        print(f"{query.tex()} evaluates to {answer}")
        self.assertTrue(answer)

        print("\nFifth query (should be True): 'For any block x, it is clear iff there is no block on it'")
        # \forall x (clear(x, s) \liff \neg exists z(on(z,s)=x))
        x = ObjVar('x')
        z = ObjVar('z')
        s = TERM['S_0']
        query = Forall(x, Iff(RelFluent("clear", x, s), Neg(Exists(z, EqAtom(ObjFluent("on", z, s), x)))))
        # f2 = bw.bat.suppress_s(query)
        # f3 = f2.flatten(VarSource())
        answer = bw.bat.entails(query, sem) # sem.eval_query(f3)
        print(f"{query.tex()} evaluates to {answer}")
        self.assertTrue(answer)


    def test_formula_transformations(self):
        import blocksworld as bw
        sigma_1 = Do(ActionTerm("move", bw.C, bw.T), bw.S_0)
        sigma_2 = Do(ActionTerm("noop"), sigma_1)
        sigma_3 = Do(ActionTerm("move", bw.A, bw.B), sigma_2)
        #sigma_4 = Do(ActionTerm("move", , ), sigma)
        q = []
        q.append(EqAtom(bw.B, ObjFluent("on", bw.A, sigma_3)))
        q.append(RelFluent("clear", ObjFluent("on", ObjFluent("on", bw.C, sigma_3), sigma_3), sigma_2))
        q.append(Neg(StaticAtom("happy", UConst("cat"))))
        q.append(Neg(EqAtom(ObjTerm("brotherOf", bw.B), ObjTerm("brotherOf", bw.C))))
        query = And(*q)
        print(f"\nQuery: ${query.tex()}$")

        # Suppress sit terms
        sup = bw.bat.suppress_s(query)
        print(f"\nSuppressed: ${sup.tex()}$")

        # Flatten
        fla = sup.flatten(VarSource())
        print(f"\nFlattened: ${fla.tex()}$")

        simp = fla.simplified_stable()
        print(f"\nSimplified, just for giggles: ${simp.tex()}$")

        # All works, fixed some bugs



if __name__ == '__main__':
    unittest.main()
