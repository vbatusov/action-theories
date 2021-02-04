# Here:
#  Causal settings for BATs
#  Causal analysis for BATs

from fol import *
from sitcalc import *
import copy

class CausalSetting(object):
    """ Consists of:
            - BAT
            - narrative (ground, executable)
            - query (uniform in s, object-closed)
    """
    def __init__(self, bat, sigma, phi):
        if not isinstance(bat, BasicActionTheory):
            raise Exception("Something wrong with the BAT.")
        if not isinstance(sigma, SitTerm) or not sigma.is_ground() or not bat.is_executable(sigma):
            raise Exception("Something wrong with the narrative.")
        if not phi.uniform_in(TERM["s"]):
            raise Exception("Query not uniform in s.")
        for v in phi.free_vars():
            if v != TERM["s"]:
                raise Exception(f"Can't have free variables in the query! {v.tex()}")

        self.bat, self.sigma, self.phi = bat, sigma, phi

    def __str__(self):
        return f"\\langle {self.sigma.tex()}, {self.phi.tex()} \\rangle"

    def precursor(self, cause):
        """ Returns the precursor of cause """
        if cause is None or cause.is_atomic():
            return None

        a = copy.deepcopy(cause.last_action())
        s = TERM["s"]
        new_phi = copy.deepcopy(self.phi)
        new_phi.replace_term(s, Do(a, s))
        new_phi = self.bat.rho(new_phi, s)
        new_phi = And(new_phi, PossAtom(a, s)).simplified_stable()
        return CausalSetting(self.bat, cause.previous_sit(), new_phi)

    def find_cause(self):
        """ Returns the sub-situation of sigma where the last action is the achievement cause of the setting """
        last_holds = None
        #print(f"Looking for a cause of {self.phi.tex()} after {self.sigma.tex()}")
        for sub in self.sigma.subsituations(reverse=True):
            #print(f"  Looking at {sub.tex()}")
            relative_query = copy.deepcopy(self.phi)
            relative_query.replace_term(TERM["s"], sub)
            #print(f"Query relativized to {sub.tex()}: {relative_query.tex()}")

            if self.bat.entails(relative_query):
                #print("This query holds")
                last_holds = sub
            else:
                #print("Query no longer holds!")
                return (last_holds, self.precursor(last_holds)) # Could be None, if setting is unachieved

        return (last_holds, self.precursor(last_holds)) # If finished loop without returning, then query holds throughout



def find_all_causes(cs):
    """ Returns all causes, in reverse chronological order, of the causal setting cs """
    pass
