from sitcalc import *
from fol import *
import semantics
import causality
#from pudb import set_trace; set_trace() # Debugger

# Create common symbols and terms
# -------------------------------
s = TERM["s"]
S_0 = TERM["S_0"]
x = ObjVar("x")
d = UConst("d")
e1 = UConst("e_1")
e2 = UConst("e_2")

# Create a basic action theory
# -------------------------------
bat = BasicActionTheory("D flip-flop")


# Add precondition axioms
# -------------------------------
ap_c_on = APA(ActionTerm("c\\_on"))
ap_tick = APA(ActionTerm("tick"), rhs=RelFluent("ClockOn", s))
ap_hi = APA(ActionTerm("hi", x), rhs=Neg(RelFluent("High", x, s)))
ap_lo = APA(ActionTerm("lo", x), rhs=RelFluent("High", x, s))

bat.add_ap_axiom(ap_c_on)
bat.add_ap_axiom(ap_tick)
bat.add_ap_axiom(ap_hi)
bat.add_ap_axiom(ap_lo)

# Add initial state axioms
# -------------------------------
init1 = InitAxiom(Neg(RelFluent("High", d, S_0)))
init2 = InitAxiom(Neg(RelFluent("High", e1, S_0)))
init3 = InitAxiom(Neg(RelFluent("High", e2, S_0)))
init4 = InitAxiom(Neg(RelFluent("En", S_0)))
init5 = InitAxiom(Neg(RelFluent("Q", S_0)))
bat.add_init_axiom(init1)
bat.add_init_axiom(init2)
bat.add_init_axiom(init3)
bat.add_init_axiom(init4)
bat.add_init_axiom(init5)


# Construct and add relational SSA
# -------------------------------
ssa_clock_on = RelSSA(RelFluent("ClockOn", s))
ssa_clock_on.add_pos_effect(ActionTerm("c\\_on"))

ssa_high = RelSSA(RelFluent("High", x, s))
ssa_high.add_pos_effect(ActionTerm("hi", x))
ssa_high.add_neg_effect(ActionTerm("lo", x))

ssa_en = RelSSA(RelFluent("En", s))
ssa_en.add_pos_effect(ActionTerm("hi", e1))
ssa_en.add_pos_effect(ActionTerm("hi", e2))
ssa_en.add_neg_effect(ActionTerm("lo", e1), context=Neg(RelFluent("High", e2, s)))
ssa_en.add_neg_effect(ActionTerm("lo", e2), context=Neg(RelFluent("High", e1, s)))

ssa_q = RelSSA(RelFluent("Q", s))
ssa_q.add_pos_effect(ActionTerm("tick"), context=And(RelFluent("En", s), RelFluent("High", d, s)))
ssa_q.add_neg_effect(ActionTerm("tick"), context=And(RelFluent("En", s), Neg(RelFluent("High", d, s))))

bat.add_ss_axiom(ssa_clock_on)
bat.add_ss_axiom(ssa_high)
bat.add_ss_axiom(ssa_en)
bat.add_ss_axiom(ssa_q)


# Add semantics; always the last thing to do
# -------------------------------
bat.add_semantics(semantics.Semantics(bat))

bat.describe()
# BAT is finished.

# Now, do interesting things with it.

# Construct the narrative
actions = [ActionTerm("c\\_on"),
            ActionTerm("hi", d),
            ActionTerm("tick"),
            ActionTerm("hi", e1),
            ActionTerm("hi", e2),
            ActionTerm("tick"),
            ActionTerm("lo", e1),
            ActionTerm("lo", e2),
            ActionTerm("tick"),
            ActionTerm("lo", d),
            ActionTerm("tick"),
            ]

sigma = build_sitterm(*actions)
query = RelFluent("Q", s)
cs = causality.CausalSetting(bat, sigma, query)

causality.find_all_causes(cs)
