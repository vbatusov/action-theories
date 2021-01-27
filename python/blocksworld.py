from sitcalc import *
from fol import *
#from pudb import set_trace; set_trace()

# Create common symbols and terms
s = TERM["s"]
S_0 = TERM["S_0"]

# Create a basic action theory
bat = BasicActionTheory("Blocks World")

# Create variables of sort Object
x = ObjVar("x")
y = ObjVar("y")
z = ObjVar("z")
# Create some action terms
move_x_y = ActionTerm("move", x, y)
move_y_z = ActionTerm("move", y, z)
move_y_x = ActionTerm("move", y, x)

# Create domain constants
T = UConst("T")
A = UConst("A")
B = UConst("B")
C = UConst("C")

# Construct subformulas and formulas
clear_x_s = RelFluent("clear", x, s)
clear_y_s = RelFluent("clear", y, s)
neq_x_y = Neg(EqAtom(x, y))
neq_x_T = Neg(EqAtom(x, T))
eq_y_T = EqAtom(y, T)
rhs = And(clear_x_s, neq_x_y, neq_x_T, Or(clear_y_s, eq_y_T))

# Add a precondition axiom for move
apa = APA(move_x_y, rhs=rhs)
bat.add_ap_axiom(apa)

# Add a precondition axiom for noop
noop = ActionTerm("noop")
bat.add_ap_axiom(APA(noop))

# Create and add initial state axioms
init1 = InitAxiom(EqAtom(ObjFluent("on", A, S_0), T).close())
init2 = InitAxiom(EqAtom(ObjFluent("on", C, S_0), B).close())
init3 = InitAxiom(EqAtom(ObjFluent("on", B, S_0), T).close())
init4 = InitAxiom(RelFluent("clear", A, S_0).close())
init5 = InitAxiom(RelFluent("clear", C, S_0).close())
init6 = InitAxiom(Neg(RelFluent("clear", B, S_0).close()))

bat.add_init_axiom(init1)
bat.add_init_axiom(init2)
bat.add_init_axiom(init3)
bat.add_init_axiom(init4)
bat.add_init_axiom(init5)
bat.add_init_axiom(init6)

# Construct and add SSA for clear (relational)
ssa_clear = RelSSA(RelFluent("clear", x, s))
ssa_clear.add_pos_effect(move_y_z, context=EqAtom(y, ObjFluent("on", x, s)))
ssa_clear.add_neg_effect(move_y_x)
bat.add_ss_axiom(ssa_clear)

# Construct and add SSA for on (functional)
ssa_on = FuncSSA(ObjFluent("on", x, s))
ssa_on.add_effect(move_x_y)
bat.add_ss_axiom(ssa_on)

# Done building the theory. Let's see it.
bat.describe()

#********************************************************************
#********************************************************************
#********************************************************************

# Test regressability
#print("\nTest regression")
w = RelFluent("clear", A, S_0)
sitterm = S_0
do_a_s = TERM["do(a,s)"]
w = RelFluent("clear", A, do_a_s)
w = PossAtom(TERM["a"], s)
w = PossAtom(move_x_y, s)

# Test APA RHS instantiation
w = PossAtom(ActionTerm("move", A, B), S_0)
irhs = bat.instantiate_ap_rhs(w)
print(f"\nInstantiating RHS wrt\n    {w.tex()}\nyields\n    {irhs.tex()}")
w = PossAtom(ActionTerm("move", A, B), do_a_s)
irhs = bat.instantiate_ap_rhs(w)
print(f"\nInstantiating RHS wrt\n    {w.tex()}\nyields\n    {irhs.tex()}")
w = PossAtom(noop, do_a_s)
print(f"\nInstantiating RHS wrt\n    {w.tex()}\nyields\n    {bat.instantiate_ap_rhs(w).tex()}")

# Test substitution
print("\nTest of general substitutions")
# A(y,x) [x/f(y), y/x] => A(x,f(y))
f_sym = Symbol("f", sort="object", sorts=["object"])
f_y = Term(f_sym, y)
at = Atom(Symbol("A", sorts=["object", "object"]), y, x)
src = [x,y]
tgt = [f_y, x]
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
w = PossAtom(ActionTerm("move", A, B), do_a_s)
print(f"Is {w.tex()} regressable to {do_a_s.tex()}? -> {bat.is_regressable_to(w, do_a_s)}")
regr = bat.rho(w, do_a_s)
print(f"Result: {regr.tex()}")
# works. Now, implement full regression (add func and rel SSA)

# Test rel SSA regression
print(f"\nUsing relational SSA")
sigma = Do(ActionTerm("move", B, T), TERM["s"]) #SitTerm(SYM["do"], ActionTerm("move", B, T), TERM["s"])
w = PossAtom(ActionTerm("move", A, B), sigma)
print(f"Is {w.tex()} regressable to {s.tex()}? -> {bat.is_regressable_to(w, s)}")
regr = bat.rho(w, s)
print(f"Result: {regr.tex()}")

# A simpler case
print(f"\nUsing relational SSA: Test 2")
w = RelFluent("clear", C, SitTerm(SYM["do"], ActionTerm("move", B, A), TERM["S_0"]))
print(f"Is {w.tex()} regressable to {S_0.tex()}? -> {bat.is_regressable_to(w, S_0)}")
regr = bat.rho(w, S_0)
print(f"Result: {regr.tex()}")
regr = regr.simplified()
print(f"Same, simplified: {regr.tex()}")

# Test functional fluent regression
print(f"\nRegression involving functional SSA: Test 1")
# B = on(A, do(move(C,T), S_0))
# "B is on A after moving C to table" (false)
query = EqAtom(B, ObjFluent("on", A, Do(ActionTerm("move", C, T), S_0)))
print(query.tex())
print(f"All terms in {regr.tex()}:")
for t in query.terms():
    if isinstance(t, FuncFluent):
        print(f"  {t.tex()} (FUNCTIONAL FLUENT TERM!!!)")
    else:
        print(f"  {t.tex()} (skip)")


regr = bat.rho(query, S_0)
print(f"Result: {regr.tex()}")
regr = regr.simplified()
print(f"Same, simplified: {regr.tex()}")

print(Fore.RED + f"\nLet's now have a regression which involves all cases!" + Style.RESET_ALL)
sigma_1 = Do(ActionTerm("move", C, T), S_0)
sigma_2 = Do(ActionTerm("noop"), sigma_1)
sigma_3 = Do(ActionTerm("move", A, B), sigma_1)
query = EqAtom(B, ObjFluent("on", A, sigma_3))
query = And(query, PossAtom(ActionTerm("move", A, B), sigma_1))
query = And(query, RelFluent("clear", C, sigma_2))
print(query.tex())
regr = bat.rho(query, S_0)
print(f"Result: {regr.tex()}")
print(f"Same, simplified: ")
print(f"{regr.simplified().tex()}")

# Implement BAT.situations() to iterate through the entire infinite tree of situations
# Finish regression and test on a ground situation term
# Semantics
# At this point, will be able to implement actual cause analysis
# Extend to hybrid case, with both FO and SO SEA
# Test on a toy domain with numerical functions (Lotka-Volterra Zayats-Volk)
# Implement regression for Hybrid
# Implement causal analysis for hybrid
