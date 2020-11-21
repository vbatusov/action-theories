import copy

class Symbol:
    """ A symbol is always a part of a theory.
        Consists of a name, sort, number and sort of arguments,
        infix - for representation only
        is_var - flags a variable symbol (Note: SOL allows function variables)
    """
    def __init__(self, name, sorts=[], sort=None, infix=False, is_var=False):
        # If no return sort, assume it's a predicate
        # Let the parent theory check for legal sorts
        if sort is None:
            self.type = "predicate"
        else:
            if is_var: # No predicate variables, don't care
                self.type = "variable"
            else:
                self.type = "function" # includes constants

        if sort is None and is_var:
            raise Exception("A variable must have a sort")
        if infix and len(sorts) != 2:
            raise Exception("An infix symbol must be binary, and this one is {}-ary".format(len(sorts)))

        self.name = name
        self.sorts = sorts
        self.arity = len(sorts)
        self.sort = sort
        self.is_var = is_var
        self.infix = infix

    def __str__(self):
        strargs = ""
        if self.arity > 0:
            strargs = "({})".format(", ".join(["<{}>".format(s) for s in self.sorts]))
        retsort = ""
        if self.type != "predicate":
            retsort = " : <{}>".format(self.sort)
        return "{}{}{} - {}".format(self.name, strargs, retsort, self.type)

    def __eq__(self, other):
        if self.name == other.name and self.sorts == other.sorts and self.sort == other.sort and self.is_var == other.is_var and self.infix == other.infix:
            return True
        return False


class RelFluentSymbol(Symbol):
    """ Must have situation as last arg. sort"""
    def __init__(self, name, sorts=[]): # sorts don't include sit term at the end
        if "situation" in sorts:
            raise Exception("Cannot have a second situation term in a relational fluent")
        Symbol.__init__(self, name, sorts=sorts+["situation"])
        self.type = "relational fluent"

class FuncFluentSymbol(Symbol):
    """ Must have situation as last arg. sort
        For now, let the sort be reals-only
    """
    def __init__(self, name, sorts=[], sort="reals"): # sorts don't include sit term at the end
        if "situation" in sorts:
            raise Exception("Cannot have a second situation term in a relational fluent")
        Symbol.__init__(self, name, sorts=sorts+["situation"], sort=sort)
        self.type = "functional fluent"

class Struct:
    """ The syntactic structure underlying
        both Term and Atom. Needed for storing methods
        common to both and thus get rid of repetition.
        Contains:
            - underlying Symbol
            - actual Struct arguments, their number and sorts
              conforming to Symbol
        Does:
            - Test for bad arguments
            - Provide iterator for all Structs therein
        Does not contain:
            - Any semantic notions, i.e., whether variable or not
    """
    def __init__(self, symbol, *args):  # args are Structs
        if len(args) != symbol.arity:
            raise TypeError("Wrong number of arguments - {} instead of {}!".format(len(args), symbol.arity))

        for s_sort, arg in zip(symbol.sorts, args):
            if s_sort != arg.sort:
                raise Exception("Wrong argument sort. Expecting {}, got {}!".format(s_sort, arg.sort()))
            if not isinstance(arg, Struct):
                raise TypeError("Struct argument is not a Struct!!")

        self.symbol = symbol
        self.args = list(args)
        # inherited from symbol for convenience
        self.sort = self.symbol.sort
        self.arity = self.symbol.arity
        self.name = self.symbol.name

    def __eq__(self, other):
        if self.symbol == other.symbol:
            # If same symbol, can safely assume arities match
            for arg1, arg2 in zip(self.args, other.args):
                if arg1 != arg2: # Recursively invoke comparison
                    return False
            return True
        return False

    def iter_structs(self): # All Atoms and Terms
        yield self
        for arg in self.args:
            for struct in arg.iter_structs():
                yield struct

    def iter_vars(self): # All Terms with is_var
        for struct in self.iter_structs():
            if struct.symbol.is_var:
                yield struct

    def symbols(self):
        yield self.symbol
        for arg in self.args:
            yield from arg.symbols()

    def replace_term(self, term, new_term):
        """ OK to put this here, because an atom can't occur as an argument
            so won't be replaced as if it were a term """
        # assume current term is not equal to 'term'
        #self.args = [new_term if term == arg else arg for arg in self.args]
        #print(f"STRUCT: replacing {term.tex()} by {new_term.tex()}")
        if not isinstance(term, Term) or not isinstance(new_term, Term):
            raise TypeError(f"One or both terms involved in substitution is not a Term!")
        if term.sort != new_term.sort:
            raise TypeError(f"Sorts of the terms don't match! Can't replace {term.sort} by {new_term.sort}")

        new_args = []
        for arg in self.args:
            if arg == term:
                new_args.append(new_term)
            else: # take care to avoid side effects when modifying arg
                new_arg = copy.deepcopy(arg)
                new_arg.replace_term(term, new_term)
                new_args.append(new_arg)
        self.args = new_args


class Term(Struct): #
    """ A term built using variables and function symbols
        For ease of use, construction should infer sorts from arguments
        Can construct term via args and sort, and infer term's symbol, if necessary
     """
    # Term(Symbol, Term, Term, ...)
    def __init__(self, symbol, *args):
        for arg in args:
            if not isinstance(arg, Term):
                raise TypeError(f"Argument {arg} is not a Term!")
        if symbol.name == "=":
            print("***Constructing and equality atom***")
        Struct.__init__(self, symbol, *args)
        self.is_var = symbol.is_var

    def __str__(self):
        return self.tex()

    def terms(self):
        yield self
        for arg in self.args:
            yield from arg.terms()

    def tex(self):
        if self.symbol.infix: # binary, already checked
            return self.name().join([arg.tex() for arg in self.args])
        if self.arity == 0:
            return self.name
        return "{}({})".format(self.symbol.name, ", ".join([arg.tex() for arg in self.args]))


class Formula(object):
    """ Any FOL wff """
    def __init__(self):
        pass
        # Nothing here

    def simplified(self):
        """ Catch-all for formulas that don't have their own simplification method """
        return self

    def free_vars(self): # will this work?
        # all vars which are not in nonfree_vars
        yield from [v for v in self.vars() if v not in self.nonfree_vars()]
        # this works, which is pretty cool, since the methods invoked
        # here exist only in subclasses of Formula

    def vars(self):
        yield from []

    def nonfree_vars(self):
        yield from []

    def terms(self):
        yield from []

    def replace_term(self, term, new_term):
        """ Covers the case where substitution is trivial """
        pass

    def tex(self):
        return ""

    def is_sentence(self):
        return not [v for v in self.free_vars()]

    def uniform_in(self, term):
        """ True iff, in self, every term of sort term.sort is term. """
        for t in self.terms():
            if t.sort == term.sort and term != t:
                return False
        return True

    def describe(self):
        if self.is_sentence():
            print("I am a sentence {}".format(self.tex()))
        else:
            print("I am an open formula {}".format(self.tex()))
        print("  My variables (in order of appearance): {}".format(", ".join([v.tex() for v in self.vars()])))
        print("  My non-free variables: {}".format(", ".join([v.tex() for v in self.nonfree_vars()])))
        print("  My free variables: {}".format(", ".join([v.tex() for v in self.free_vars()])))

class Tautology(Formula):
    def tex(self):
        return "\\top"

class Contradiction(Formula):
    def tex(self):
        return "\\bot"

class Atom(Formula, Struct):
    """ Atomic formula """
    def __init__(self, symbol, *args): # args must be Terms
        if symbol.sort is not None:
            raise TypeError("Cannot make an atom out of {}".format(str(symbol)))
        for arg in args:
            if not isinstance(arg, Term):
                raise TypeError("Atom's arguments must be Terms!")

        Formula.__init__(self)
        Struct.__init__(self, symbol, *args)

    # Having free_vars and non_free vars requires duplication of logic
    # Better define vars and nonfree_vars, and get free_vars by difference
    def vars(self): # generator
        # All variables in an atom are free
        for var in self.iter_vars():
            yield var

    def nonfree_vars(self): # generator
        return # It's an atom
        yield

    def replace_term(self, term, new_term):
        """ Use Struct's, and not Formula's, because Atom inherits from both"""
        Struct.replace_term(self, term, new_term)

    def tex(self):
        if len(self.args) > 0:
            return "{}({})".format(self.symbol.name, ", ".join([arg.tex() for arg in self.args]))
        return self.symbol.name

class EqAtom(Atom):
    """ Might have to exclude the = symbol from all theories' vocabularies!
        Might have to look over all conditions that depend on isinstance(_, Atom)!
    """
    def __init__(self, *args):
        if len(args) != 2:
            raise TypeError(f"Equality must have two arguments, {len(args)} given.")
        if args[0].sort != args[1].sort:
            raise TypeError(f"Cannot equate terms of distinct sorts! {args[0].sort} vs. {args[1].sort}")

        #print(f"Constructing EqAtom using {args[0].tex()} and {args[1].tex()}")
        #print(f"Sorts: args[0] is {args[0].sort}, args[1] is {args[1].sort}")

        symbol = Symbol("=", sorts=[args[0].sort]*2) # Might have to exclude this from theory's vocabulary
        Atom.__init__(self, symbol, *args)

    def tex(self):
        return f"{self.args[0].tex()} \\eq {self.args[1].tex()}"

class Neg(Formula): # negation
    def __init__(self, formula):
        Formula.__init__(self)
        # No constraints. Any formula can be negated.
        self.formula = formula

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        tmp = self.formula.simplified()
        if isinstance(tmp, Contradiction):
            return Tautology()
        elif isinstance(tmp, Tautology):
            return Contradiction()
        elif isinstance(tmp, Neg):
            return tmp.formula
        else:
            return self

    def vars(self): # generator
        # All variables in an atom are free
        yield from self.formula.vars()

    def nonfree_vars(self): # generator
        yield from self.formula.nonfree_vars()

    def symbols(self):
        yield from self.formula.symbols()

    def terms(self):
        yield from self.formula.terms()

    def replace_term(self, term, new_term):
        #print(f"Negation: replacing {term.tex()} by {new_term.tex()}")
        self.formula.replace_term(term, new_term)

    def tex(self):
        if isinstance(self.formula, Junction) or isinstance(self.formula, EqAtom):
            return "\\neg ({})".format(self.formula.tex())
        else:
            return "\\neg {}".format(self.formula.tex())

class Junction(Formula):
    def __init__(self, *formulas): # a list of formulas in junction
        Formula.__init__(self)
        #if len(formulas) < 2:
        #    raise Exception("A binary connective needs at least two formulas!")
        # Let's relax this a bit --- allow empty junctions, handle depending on child class

        self.formulas = list(formulas)

    def vars(self): # generator
        for f in self.formulas:
            yield from f.vars()

    def nonfree_vars(self): # generator
        for f in self.formulas:
            yield from f.nonfree_vars()

    def symbols(self):
        for f in self.formulas:
            yield from f.symbols()

    def terms(self):
        for f in self.formulas:
            yield from f.terms()

    def replace_term(self, term, new_term):
        #print(f"Junction: replacing {term.tex()} by {new_term.tex()}")
        for f in self.formulas:
            f.replace_term(term, new_term)

    def tex(self, connective):
        joiner = " \\{} ".format(connective)
        return joiner.join([f.tex() for f in self.formulas])


class And(Junction):
    def __new__(cls, *formulas, **kwargs):
        if len(formulas) == 0:
            return Tautology()
        elif len(formulas) == 1:
            return formulas[0]
        else:
            return super().__new__(cls) #, *formulas, **kwargs)

    def __init__(self, *formulas):
        Junction.__init__(self, *formulas)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        new_formulas = []
        for f in self.formulas:
            tmp = f.simplified()
            if isinstance(tmp, Contradiction):
                return tmp
            elif isinstance(tmp, Tautology):
                pass
            else:
                new_formulas.append(tmp)
        return And(*new_formulas)

    def tex(self):
        texes = ["({})".format(f.tex()) if isinstance(f, Or) else f.tex() for f in self.formulas]
        return " \\land ".join(texes)

class Or(Junction):
    def __new__(cls, *formulas, **kwargs):
        if len(formulas) == 0:
            return Contradiction()
        elif len(formulas) == 1:
            return formulas[0]
        else:
            return super().__new__(cls)

    def __init__(self, *formulas):
        Junction.__init__(self, *formulas)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        new_formulas = []
        for f in self.formulas:
            tmp = f.simplified()
            if isinstance(tmp, Contradiction):
                pass
            elif isinstance(tmp, Tautology):
                return tmp
            else:
                new_formulas.append(tmp)
        return Or(*new_formulas)

    def tex(self):
        texes = ["({})".format(f.tex()) if isinstance(f, And) else f.tex() for f in self.formulas]
        return " \\lor ".join(texes)

class Implies(Junction):
    def __init__(self, *formulas):
        if len(formulas) != 2:
            raise Exception("Implication must be binary!")
        Junction.__init__(self, *formulas)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        premise = self.formulas[0].simplified()
        conclusion = self.formulas[1].simplified()
        if isinstance(premise, Tautology):
            return conclusion
        elif isinstance(premise, Contradiction):
            return Tautology()
        elif isinstance(conclusion, Tautology):
            return conclusion
        elif isinstance(conclusion, Contradiction):
            return Neg(premise).simplified()
        else:
            return Implies(premise, conclusion)


    def tex(self):
        tex1 = "({})".format(self.formulas[0].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[0].tex()
        tex2 = "({})".format(self.formulas[1].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[1].tex()
        return "{} \\to {}".join(tex1, tex2)

class Iff(Junction):
    def __init__(self, *formulas):
        if len(formulas) != 2:
            raise Exception("Bidirectional implication must be binary!")
        Junction.__init__(self, *formulas)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self """
        left = self.formulas[0].simplified()
        right = self.formulas[1].simplified()
        if isinstance(left, Tautology):
            return right
        elif isinstance(left, Contradiction):
            return Neg(right).simplified()
        elif isinstance(right, Tautology):
            return left
        elif isinstance(right, Contradiction):
            return Neg(left).simplified()
        else:
            return Iff(left, right)

    def tex(self):
        tex1 = "({})".format(self.formulas[0].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[0].tex()
        tex2 = "({})".format(self.formulas[1].tex()) if isinstance(self.formulas[0], Junction) else self.formulas[1].tex()
        return "{} \\liff {}".format(tex1, tex2)

class Quantified(Formula):
    """ <quantifier> var (formula) """
    def __init__(self, var, formula):
        Formula.__init__(self)
        # var should be a Variable
        # formula should be a well-formed formula
        # formula cannot quantify over var (throw exc.)
        if not var.is_var:
            raise Exception("{} is not a variable, cannot quantify over it!".format(str(var)))
        if var in formula.nonfree_vars():
            raise Exception("Formula {} already quantifies over {}".format(formula.tex(), var.tex()))
        # This code is suspect, revise after testing all of the above
        elif var not in formula.vars():
            print("Warning: formula {} does not have free {} to quantify over!".format(formula.tex(), var.tex()))
        self.var = var
        self.formula = formula

    def vars(self): # generator
        yield from self.formula.vars()

    def nonfree_vars(self): # generator
        yield self.var
        yield from self.formula.nonfree_vars()

    def symbols(self):
        yield self.var.symbol
        yield from self.formula.symbols()

    def terms(self):
        yield from self.formula.terms()

    def replace_term(self, term, new_term):
        #print(f"Quantified {self.var}: replacing {term.tex()} by {new_term.tex()}")
        self.formula.replace_term(term, new_term)

    def tex(self, quantifier):
        template = "\\{} {} {}"
        if isinstance(self.formula, Junction) or isinstance(self.formula, EqAtom):
            template = "\\{} {} ({})"
        return template.format(quantifier, self.var.tex(), self.formula.tex())

class Forall(Quantified):
    """ \\forall var (formula) """
    def __init__(self, var, formula):
        Quantified.__init__(self, var, formula)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self
            Don't bother simplifying quantifiers for now """
        tmp = self.formula.simplified()
        if isinstance(tmp, Contradiction) or isinstance(tmp, Tautology):
            return tmp
        else:
            return Forall(self.var, self.formula.simplified())

    def tex(self):
        return Quantified.tex(self, "forall")

class Exists(Quantified):
    """ \\exists var (formula) """
    def __init__(self, var, formula):
        Quantified.__init__(self, var, formula)

    def simplified(self):
        """ Returns a shallow syntactic simplification of self
            Don't bother simplifying quantifiers for now """
        tmp = self.formula.simplified()
        if isinstance(tmp, Contradiction) or isinstance(tmp, Tautology):
            return tmp
        else:
            return Exists(self.var, self.formula.simplified())

    def tex(self):
        return Quantified.tex(self, "exists")

class RelSSA(Formula):
    """ Successor state axiom for a relational fluent
        Custom-form FOL formula for Basic Action Theories
        Constructor only takes a relational fluent symbol and terms for variables
        The RHS is constructed sequentially by adding positive and negative effects
    """
    def __init__(self, symbol, obj_vars=[], voc={}):
        """ Classic Reiter's SSA
            F(\\bar{x}, do(a,s)) \liff [disj. of pos. effects] \lor F(\bar{x}, s)
              \land \neg [disj. of neg. effects]
            obj_vars are the \\bar{x}
            voc is the vocabulary containing terms 'do(a,s)', 'a', 's'
        """
        # Must maintain the pieces and the total formula in sync!
        if not isinstance(symbol, RelFluentSymbol):
            raise Exception("A relational SSA must be about a relational fluent")

        for v in obj_vars:
            if v.sort != "object":
                raise TypeError("Fluent object arguments must be of sort object")

        self.a_var = voc['a']
        self.s_var = voc['s']
        # Create universally quantified variables
        lhs_atom_args = obj_vars + [voc['do(a,s)']]
        rhs_atom_args = obj_vars + [voc['s']]

        self.obj_vars = obj_vars
        self.univ_vars = obj_vars + [voc['a'], voc['s']]
        self.lhs = Atom(symbol, *lhs_atom_args)
        self.frame_atom = Atom(symbol, *rhs_atom_args)
        self.pos_effects = []
        self.neg_effects = []
        self.formula = None # this is just to indicate where the formula can be found
        self._build_formula() # reconcile bits into one formula

    def simplified(self):
        raise Exception("Not supposed to do this on a SSA")

    def replace_term(self, term, new_term):
        raise Exception("Not supposed to do this on a SSA")

    def _build_formula(self):
        p_eff = Or(*self.pos_effects)
        n_eff = Or(*self.neg_effects)
        frame = And(self.frame_atom, Neg(n_eff))
        rhs = Or(p_eff, frame)
        iff = Iff(self.lhs, rhs)

        quantified = iff
        for var in reversed(self.univ_vars):
            quantified = Forall(var, quantified)

        self.formula = quantified.simplified()

        if not self.formula.is_sentence():
            raise Exception("Resulting SSA is not a sentence. Perhaps an extra var in effects?")

    def _effect_type_check(self, action, context):
        if not isinstance(action, Term) or action.sort != "action":
            raise TypeError(f"Bad action term {action.tex()}!")
        if not isinstance(context, Formula):
            raise TypeError(f"Bad context formula {context.tex()}!")
        for a_arg in action.args:
            if a_arg.sort != "object":
                raise TypeError(f"Action term {action.tex()} has non-object arguments!")

    def _add_effect(self, action, context, positive=True):
        """ action: fully instantiated action term with variables among obj_vars
                (other vars will be existentially quantified, automatically)
            context: arbitrary formula uniform in s with free variables among obj_vars
            (a=action_name(\bar{x}) \land \Phi(\bar{x},s))
        """
        self._effect_type_check(action, context)
        eq = EqAtom(self.a_var, action)
        effect = And(eq, context)
        # All vars not occurring on LHS will get existentially quantified
        for v in effect.free_vars():
            if v not in self.univ_vars:
                effect = Exists(v, effect)

        effect = effect.simplified()
        if not effect.uniform_in(self.s_var):
            raise Exception(f"Effect {effect.tex()} not uniform in s!")

        if positive:
            self.pos_effects.append(effect)
        else:
            self.neg_effects.append(effect)
        self._build_formula()

    def add_pos_effect(self, action, context):
        self._add_effect(action, context, positive=True)


    def add_neg_effect(self, action, context):
        self._add_effect(action, context, positive=False)

    def describe(self):
        self.formula.describe()

    def tex(self):
        return self.formula.tex()



class FuncSSA(Formula): # Version with no common ancestor w/ RelSSA
    """ Successor state axiom for a functional fluent
        Custom-form FOL formula for Basic Action Theories
        Constructor only takes a functional fluent symbol and terms for variables
        The RHS is constructed sequentially by adding effects
    """
    def __init__(self, symbol, obj_vars=[], voc={}):
        """ Classic Reiter's SSA
            f(\\bar{x}, do(a,s)) = y \liff [disj. of effects wrt y] \lor y = f(\bar{x}, s)
              \land \neg \exists y' [disj. of effects wrt y']
            obj_vars are the \\bar{x}
            voc is the vocabulary containing terms 'do(a,s)', 'a', 's'
            y and y' are created here, not passed as arguments
        """
        if not isinstance(symbol, FuncFluentSymbol):
            raise Exception("A functional SSA must be about a functional fluent")

        for v in obj_vars:
            if v.sort != "object":
                raise TypeError("Fluent object arguments must be of sort object")

        # Remember the important standard symbols for easy access
        self.a_var = voc['a']
        self.s_var = voc['s']

        # Create universally quantified variables for the fluent eq-atom on both sides
        self.lhs_atom_args = obj_vars + [voc['do(a,s)']]
        self.rhs_atom_args = obj_vars + [voc['s']]


        # The RHS of equality, the distinguished y and y' variables
        # Must check for collisions with object variables and with effect variables (even if quantified?)
        self.y = Term(Symbol("y", sort=symbol.sort, is_var=True))
        self.y_ = Term(Symbol("y'", sort=symbol.sort, is_var=True))

        if self.y.name in [v.name for v in obj_vars]:
            # This is, in fact, allowed in first-order logic - having two variables of same name but different Sorts
            # However, they will look identical in formulas, so let's rule this out
            raise Exception("Variable 'y' is reserved in functional SSA! Can't use for an argument.")

        # \bar{x} - just the object argument variables
        self.obj_vars = obj_vars
        # All implicitly quantified variables
        self.univ_vars = obj_vars + [self.y, voc['a'], voc['s']]

        # Build the actual func. fluent terms
        self.lhs_fluent = Term(symbol, *self.lhs_atom_args)
        self.rhs_fluent = Term(symbol, *self.rhs_atom_args)
        # LHS equality
        self.lhs = EqAtom(self.lhs_fluent, self.y)
        # RHS equality
        self.frame_atom = EqAtom(self.y, self.rhs_fluent)

        # For func. fluents, all effects are both positive and negative
        self.effects = []

        self.formula = None # this is just to indicate where the formula can be found
        self._build_formula() # reconcile bits into one formula

    def simplified(self):
        raise Exception("Not supposed to do this on a SSA")

    def _build_formula(self): # Revise completely
        p_eff = Or(*self.effects)
        n_eff = Or(*self.effects)
        n_eff.replace_term(self.y, self.y_) # Replace y by y'
        # Resume from here vvvvv

        frame = And(self.frame_atom, Neg(Exists(self.y_, n_eff)))
        rhs = Or(p_eff, frame)
        iff = Iff(self.lhs, rhs)

        quantified = iff
        for var in reversed(self.univ_vars):
            quantified = Forall(var, quantified)

        self.formula = quantified.simplified()

        if not self.formula.is_sentence():
            #self.formula.describe()
            raise Exception("Resulting SSA is not a sentence. Perhaps an extra var in effects?")

    def _effect_type_check(self, action, context):
        if not isinstance(action, Term) or action.sort != "action":
            raise TypeError(f"Bad action term {action.tex()}!")
        if not isinstance(context, Formula):
            raise TypeError(f"Bad context formula {context.tex()}!")
        for a_arg in action.args:
            if a_arg.sort != "object":
                raise TypeError(f"Action term {action.tex()} has non-object arguments!")

    def _add_effect(self, action, context):
        """ action: fully instantiated action term with variables among obj_vars
                (other vars will be existentially quantified, automatically)
            context: arbitrary formula uniform in s with free variables among obj_vars
            (a=action_name(\bar{x}) \land \Phi(\bar{x},s))
            EFFECT MUST MENTION y!!!!!!!!
        """
        self._effect_type_check(action, context)
        eq = EqAtom(self.a_var, action)
        effect = And(eq, context)
        # All vars not occurring on LHS will get existentially quantified
        for v in effect.free_vars():
            if v not in self.univ_vars:
                effect = Exists(v, effect)

        effect = effect.simplified()
        if not effect.uniform_in(self.s_var):
            raise Exception(f"Effect {effect.tex()} not uniform in s!")

        if positive:
            self.pos_effects.append(effect)
        else:
            self.neg_effects.append(effect)
        self._build_formula()

    def add_pos_effect(self, action, context):
        self._add_effect(action, context, positive=True)


    def add_neg_effect(self, action, context):
        self._add_effect(action, context, positive=False)

    def describe(self):
        self.formula.describe()

    def tex(self):
        return self.formula.tex()
