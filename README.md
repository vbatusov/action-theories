# Action Theories

This project allows for programmatic creation of basic action theories of situation calculus as per Raymond Reiter's definition in *Knowledge in Action (2001)*.

Why? Because even a simple BAT quickly turns into a mess of axioms which are impossible to troubleshoot, let alone regress.

## Overview
- Can create situation calculus formulas and theories in code
- Can regress queries of arbitrary complexity through situations of arbitrary complexity
- Automatic formula simplification
- Outputs clean LaTeX of the final result
- Can handle both relational and functional fluents and SSA, unlike all we've ever had
- Uses Prolog for semantic back-end, but doesn't have to. Implement your own semantics, even if by just hard-coding the meaning of sentences.

## Module `fol.py`
Implements all things related to the syntax of many-sorted first-order logic with equality.
- `Symbol` A token with a sort and an arity with sorts. Used for all non-variable atomic structs of the language.
- `Struct` A struct is a concrete structure underlying both `Term` and `Atom`
    - `Term` **A FOL term** (function or constant)
        - `NumTerm` *Not implemented yet*
- `Formula` A formula of arbitrary complexity
    - `Atom(Formula, Struct)` **Atomic FOL formula**
        - `EqAtom` **Equality atom**
    - `Neg` A negation formula
    - `Junction` Any kind of junction formula
        - `And` Conjunction
        - `Or` Disjunction
        - `Implies` Implication
        - `Iff` Bidirectional implication
    - `Quantified` Generic quantified formula
        - `Exists` Existentially-quantified
        - `Forall` Universally-quantified
    - `Contradiction` and `Tautology` Structureless, either contradiction or tautology
- `Axiom` A generic axiom. Must contain a formula.
- `Theory` Contains a collection of axioms and a `Semantics` object to make sense of them.

## Module `sitcalc.py`

Implements specifically situation calculus structures. Situation calculus contains default sorts *object*, *action*, *situation*

- `UConst(Term)` A constant with a unique name
- `ObjVar(Term)` A variable of sort *object* (most common)
- `StaticAtom(Atom)` Situation-independent atom
- `ActionTerm(Term)` Action term
- `SitTerm(Term)` Generic situation term. Provides an iterator over sub-situations.
- `Do(SitTerm)` A sit. term constructed using the function *do*
- `PossAtom(Atom)` A *Poss* atom as used by Reiter for precondition axioms.
- `Fluent(object)` Abstract fluent class
    - `RelFluent(Atom, Fluent)` Relational fluent atom
    - `FuncFluent(Term, Fluent)` Functional fluent term
        - `ObjFluent(FuncFluent)` Func. fluent of sort *object*
- `Axiom` (see `fol.py`)
    - `InitAxiom(Axiom)` Initial state axiom, i.e., any FOL sentence uniform in S_0
    - `APA(Axiom)` Action precondition axiom
    - `SSA(Axiom)` Successor state axiom
        - `RelSSA(SSA)` A successor state axiom for a relational fluent
        - `FuncSSA(SSA)` A successor state axiom for a functional fluent
- `Theory` (see `fol.py`)
    - `BasicActionTheory(Theory)` A container for all things which constitute a consistent basic action theory. Offers methods for suppressing situation terms, checking executability, regressability, etc. Implements `rho`, the single-step regression operator.
        - `HybridTheory(BasicActionTheory)` A hybrid basic action theory. *Not yet implemented*

## Module `causality.py`

Implements actual cause analysis on causal settings. Causal analysis requires a consistent BAT with semantics.

- `CausalSetting(object)` A class to represent a causal setting, which consists of a BAT, a ground situation term, and a query. `CausalSetting.find_cause()` returns the achievement cause, `CausalSetting.precursor(cause)` returns the corresponding causal precursor.

## Module `semantics.py`

Uses `pyswip` to implement FOL semantics for action theories as described above. Clearly, this is not full-blown FOL semantics, so the modeller must take care not to venture outside of the fragment, or else implement own semantics.

Module operates by literally translating the axioms of a BAT to Prolog clauses and asserting them to an internal knowledge base. Queries are likewise translated and posed against the KB.

Key method is `Semantics.eval_query(query)`.

# Examples
`blocksworld.py` contains the classic Blocks World axiomatization.

`flipflop.py` contains the D flip-flop example from the 2018 AAAI paper.

Run `python tests.py` to see various tests.

## Formula building example
```
x = ObjVar('x')
z = ObjVar('z')
s = TERM['S_0']
query = Forall(x, Implies(Exists(z, EqAtom(ObjFluent("on", z, s), x)), Neg(RelFluent("clear", x, s))))
```
This constructs a formula whose `.tex()` representation is

`\forall x (\exists z (on(z, S_0) \eq x) \to \neg clear(x, S_0))`

and meaning "In initial situation S_0, every block which has something on it is not clear".

To evaluate the query against the Blocks World BAT:
```
import blocksworld as bw
answer = bw.bat.entails(query)
```
