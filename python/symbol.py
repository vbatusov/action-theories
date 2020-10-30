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
    """ Must have situation as last arg. sort"""
    def __init__(self, name, sorts=[], sort="reals"): # sorts don't include sit term at the end
        if "situation" in sorts:
            raise Exception("Cannot have a second situation term in a relational fluent")
        Symbol.__init__(self, name, sorts=sorts+["situation"], sort=sort)
        self.type = "functional fluent"
