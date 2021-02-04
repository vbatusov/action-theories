from sitcalc import *
from fol import *
import semantics
#from pudb import set_trace; set_trace() # Debugger

# Create common symbols and terms
# -------------------------------
s = TERM["s"]
S_0 = TERM["S_0"]


# Create a basic action theory
# -------------------------------
# bat = BasicActionTheory("Name")


# Add precondition axioms
# -------------------------------
# apa = APA(move_x_y, rhs=rhs)
# bat.add_ap_axiom(apa)


# Add initial state axioms
# -------------------------------
# init = InitAxiom( ... )
# bat.add_init_axiom(init)


# Construct and add relational SSA
# -------------------------------
# ssa = RelSSA( ... )
# ssa.add_pos_effect( ... , context=...)
# ssa.add_neg_effect( ... )
# bat.add_ss_axiom(ssa)


# Construct and add functional SSA
# -------------------------------
# ssa = FuncSSA( ... )
# ssa.add_effect( ... )
# bat.add_ss_axiom(ssa)


# Add semantics; always the last thing to do
# -------------------------------
bat.add_semantics(semantics.Semantics(bat))
