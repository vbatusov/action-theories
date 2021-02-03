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
# Meaning: on(x) = y iff x is on y
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




# At this point, will be able to implement actual cause analysis


# Extend to hybrid case, with both FO and SO SEA
# Test on a toy domain with numerical functions (Lotka-Volterra Zayats-Volk)
# Implement regression for Hybrid
# Implement causal analysis for hybrid
