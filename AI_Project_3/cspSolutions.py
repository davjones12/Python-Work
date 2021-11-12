# import cspSearch
from cspSearch import dfs_solver
from cspProblem import MapColoringCSP, Constraint, NQueensColoringCSP
from operator import lt, ne, eq, gt
from cspExamples import ne_
from display import Displayable

from searchProblem import Arc, Search_problem


class Con_solver(Displayable):
    """Solves a CSP with arc consistency and domain splitting
    """

    def __init__(self, csp, **kwargs):
        """a CSP solver that uses arc consistency
        * csp is the CSP to be solved
        * kwargs is the keyword arguments for Displayable superclass
        """
        self.csp = csp
        super().__init__(**kwargs)  # Or Displayable.__init__(self,**kwargs)

    def make_arc_consistent(self, orig_domains=None, to_do=None):
        """Makes this CSP arc-consistent using generalized arc consistency
        orig_domains is the original domains
        to_do is a set of (variable,constraint) pairs
        returns the reduced domains (an arc-consistent variable:domain dictionary)
        """
        if orig_domains is None:
            orig_domains = self.csp.domains
        if to_do is None:
            to_do = {(var, const) for const in self.csp.constraints
                     for var in const.scope}
        else:
            to_do = to_do.copy()  # use a copy of to_do
        domains = orig_domains.copy()
        self.display(2, "Performing AC with domains", domains)
        while to_do:
            var, const = self.select_arc(to_do)
            self.display(3, "Processing arc (", var, ",", const, ")")
            other_vars = [ov for ov in const.scope if ov != var]
            new_domain = {val for val in domains[var]
                          if self.any_holds(domains, const, {var: val}, other_vars)}
            if new_domain != domains[var]:
                self.display(4, "Arc: (", var, ",", const, ") is inconsistent")
                self.display(3, "Domain pruned", "dom(", var, ") =", new_domain,
                             " due to ", const)
                domains[var] = new_domain
                add_to_do = self.new_to_do(var, const) - to_do
                to_do |= add_to_do  # set union
                self.display(3, "  adding", add_to_do if add_to_do else "nothing", "to to_do.")
            self.display(4, "Arc: (", var, ",", const, ") now consistent")
        self.display(2, "AC done. Reduced domains", domains)
        return domains

    def new_to_do(self, var, const):
        """returns new elements to be added to to_do after assigning
        variable var in constraint const.
        """
        return {(nvar, nconst) for nconst in self.csp.var_to_const[var]
                if nconst != const
                for nvar in nconst.scope
                if nvar != var}

    def select_arc(self, to_do):
        """Selects the arc to be taken from to_do .
        * to_do is a set of arcs, where an arc is a (variable,constraint) pair
        the element selected must be removed from to_do.
        """
        return to_do.pop()

    def any_holds(self, domains, const, env, other_vars, ind=0):
        """returns True if Constraint const holds for an assignment
        that extends env with the variables in other_vars[ind:]
        env is a dictionary
        Warning: this has side effects and changes the elements of env
        """
        if ind == len(other_vars):
            return const.holds(env)
        else:
            var = other_vars[ind]
            for val in domains[var]:
                # env = dict_union(env,{var:val})  # no side effects!
                env[var] = val
                if self.any_holds(domains, const, env, other_vars, ind + 1):
                    return True
            return False

    def solve_one(self, domains=None, to_do=None):
        """return a solution to the current CSP or False if there are no solutions
        to_do is the list of arcs to check
        """
        if domains is None:
            domains = self.csp.domains
        new_domains = self.make_arc_consistent(domains, to_do)
        if any(len(new_domains[var]) == 0 for var in domains):
            return False
        elif all(len(new_domains[var]) == 1 for var in domains):
            self.display(2, "solution:", {var: select(
                new_domains[var]) for var in new_domains})
            return {var: select(new_domains[var]) for var in domains}
        else:
            var = self.select_var(x for x in self.csp.variables if len(new_domains[x]) > 1)
            if var:
                dom1, dom2 = partition_domain(new_domains[var])
                self.display(3, "...splitting", var, "into", dom1, "and", dom2)
                new_doms1 = copy_with_assign(new_domains, var, dom1)
                new_doms2 = copy_with_assign(new_domains, var, dom2)
                to_do = self.new_to_do(var, None)
                self.display(3, " adding", to_do if to_do else "nothing", "to to_do.")
                return self.solve_one(new_doms1, to_do) or self.solve_one(new_doms2, to_do)

    def select_var(self, iter_vars):
        """return the next variable to split"""
        return select(iter_vars)


def partition_domain(dom):
    """partitions domain dom into two.
    """
    split = len(dom) // 2
    dom1 = set(list(dom)[:split])
    dom2 = dom - dom1
    return dom1, dom2


def copy_with_assign(domains, var=None, new_domain={True, False}):
    """create a copy of the domains with an assignment var=new_domain
    if var==None then it is just a copy.
    """
    newdoms = domains.copy()
    if var is not None:
        newdoms[var] = new_domain
    return newdoms


def select(iterable):
    """select an element of iterable. Returns None if there is no such element.

    This implementation just picks the first element.
    For many of the uses, which element is selected does not affect correctness,
    but may affect efficiency.
    """
    for e in iterable:
        return e  # returns first element found


class Search_with_AC_from_CSP(Search_problem, Displayable):
    """A search problem with arc consistency and domain splitting

    A node is a CSP """

    def __init__(self, csp):
        self.cons = Con_solver(csp)  # copy of the CSP
        self.domains = self.cons.make_arc_consistent()

    def is_goal(self, node):
        """node is a goal if all domains have 1 element"""
        return all(len(node[var]) == 1 for var in node)

    def start_node(self):
        return self.domains

    def neighbors(self, node):
        """returns the neighboring nodes of node.
        """
        neighs = []
        var = select(x for x in node if len(node[x]) > 1)
        if var:
            dom1, dom2 = partition_domain(node[var])
            self.display(2, "Splitting", var, "into", dom1, "and", dom2)
            to_do = self.cons.new_to_do(var, None)
            for dom in [dom1, dom2]:
                newdoms = copy_with_assign(node, var, dom)
                cons_doms = self.cons.make_arc_consistent(newdoms, to_do)
                if all(len(cons_doms[v]) > 0 for v in cons_doms):
                    # all domains are non-empty
                    neighs.append(Arc(node, cons_doms))
                else:
                    self.display(2, "...", var, "in", dom, "has no solution")
        return neighs


def ac_search_solver(csp):
    """arc consistency (search interface)"""
    sol = Searcher(Search_with_AC_from_CSP(csp)).search()
    if sol:
        return {v: select(d) for (v, d) in sol.end().items()}


def dict_union(d1, d2):
    """returns a dictionary that contains the keys of d1 and d2.
    The value for each key that is in d2 is the value from d2,
    otherwise it is the value from d1.
    This does not have side effects.
    """
    d = dict(d1)  # copy d1
    d.update(d2)
    return d


# ************ PROBLEM #1: MAP COLORING ************

# Australia: There are 7 states/teritories. Tasmania does not have any neighbors. Three colors suffice.
# australia_csp = MapColoringCSP(list('RGB'), """SA: WA NT Q NSW V; NT: WA Q; NSW: Q V; T: """)

# USA, 4 colors needed.

# usa_csp = MapColoringCSP(list('RGBY'), """WA: OR ID; OR: ID NV CA; CA: NV AZ; NV: ID UT AZ; ID: MT WY UT; UT: WY CO AZ; MT: ND SD WY; WY: SD NE CO; CO: NE KA OK NM; NM: OK TX AZ; ND: MN SD; SD: MN IA NE; NE: IA MO KA; KA: MO OK; OK: MO AR TX; TX: AR LA; MN: WI IA; IA: WI IL MO; MO: IL KY TN AR; AR: MS TN LA; LA: MS; WI: MI IL; IL: IN KY; IN: OH KY; MS: TN AL; AL: TN GA FL; MI: OH IN; OH: PA WV KY; KY: WV VA TN; TN: VA NC GA; GA: NC SC FL; PA: NY NJ DE MD WV; WV: MD VA; VA: MD DC NC; NC: SC; NY: VT MA CT NJ; NJ: DE; DE: MD; MD: DC; VT: NH MA; MA: NH RI CT; CT: RI; ME: NH; HI: ; AK: """)

# France, 4 colors needed.
# france_csp = MapColoringCSP(list('RGBY'), """AL: LO FC; AQ: MP LI PC; AU: LI CE BO RA LR MP; BO: CE IF CA FC RA AU; BR: NB PL; CA: IF PI LO FC BO; CE: PL NB NH IF BO AU LI PC; FC: BO CA LO AL RA; IF: NH PI CA BO CE; LI: PC CE AU MP AQ; LO: CA AL FC; LR: MP AU RA PA; MP: AQ LI AU LR; NB: NH CE PL BR; NH: PI IF CE NB; NO: PI; PA: LR RA; PC: PL CE LI AQ; PI: NH NO CA IF; PL: BR NB CE PC; RA: AU BO FC PA LR""")

def solveMapColoringCSP(colors: list, neighbors: str):
    solution = ac_search_solver(MapColoringCSP(colors, neighbors))
    return solution


# ********PROBLEM #2: Zebra Puzzle - Basic Problem *************


def blue_check(a, b, c, d, e, f):
    if a == "blue" and b == "Norwegian":  # this set meets the criteria
        return True
    else:
        if c == "blue" and d == "Norwegian":
            return True
        else:
            if e == "blue" and f == "Norwegian":
                return True
            else:
                return False


def red_check(a, b, c, d):
    """is true if the letters concatenated form a word in words"""
    if a == "red" and b == "Spanish":
        return True
    else:
        if c == "red" and d == "Spanish":
            return True
        else:
            return False


def solveZebraBasic():
    color = {'blue', 'red', 'white'}
    nation = {'Norwegian', 'Italian', 'Spanish'}

    zebra_csp = ZebraPuzzleCSP(
        {'p11': {'House1'}, 'p12': {'House2'}, 'p13': {'House3'}, 'p21': color, 'p22': color, 'p23': color,
         'p31': nation,
         'p32': nation, 'p33': nation},
        [ZConstraint(('p31',), ne_('Italian'), "p31 != 'Italian'"),
         ZConstraint(('p33',), ne_('Italian'), "p33 != 'Italian'"),
         ZConstraint(('p21', 'p22'), ne, "p21 != p22"),
         ZConstraint(('p22', 'p23'), ne, "p22 != p23"),
         ZConstraint(('p21', 'p23'), ne, "p21 != p23"),
         ZConstraint(('p31', 'p32'), ne, "p31 != p32"),
         ZConstraint(('p32', 'p33'), ne, "p32 != p33"),
         ZConstraint(('p31', 'p33'), ne, "p31 != p33"),
         ZConstraint(('p21', 'p31', 'p22', 'p32', 'p23', 'p33'), blue_check, "blue_check_1(p21,p31,p22,p32,p23,p33)"),
         ZConstraint(('p21', 'p32', 'p22', 'p33'), red_check, "red_check(p21, p32, p22, p33)"),
         ZConstraint(('p31',), ne_('Spanish'), "p31 != 'Spanish'")])

    solution = ac_search_solver(zebra_csp)
    finaldict = dict()
    finaldict[1] = []
    finaldict[2] = []
    finaldict[3] = []

    a = list()
    b = list()
    c = list()

    for i in solution:
        if i[2] == '1':
            a.append(solution.get(i))
        elif i[2] == '2':
            b.append(solution.get(i))
        elif i[2] == '3':
            c.append(solution.get(i))

    a.remove('House1')
    b.remove('House2')
    c.remove('House3')

    finaldict[1] = a
    finaldict[2] = b
    finaldict[3] = c

    return finaldict


# ********PROBLEM #2: Zebra Puzzle - Movie Nights **********

shirt = {'black', 'blue', 'green', 'red'}
name = {'Daniel', 'Joshua', 'Nicholas', 'Ryan'}
movie = {'action', 'comedy', 'horror', 'thriller'}
snack = {'chips', 'cookies', 'crackers', 'popcorn'}
age = {'11 years', '12 years', '13 years', '14 years'}


def notEqualSuper(a, b, c, d):
    complist = list()
    complist.append(a)
    complist.append(b)
    complist.append(c)
    complist.append(d)

    seen = set()
    for x in complist:
        if x in seen:
            return False
        seen.add(x)

    return True


"""
1. Joshua is in one of the ends.
"""

def rule_one(a, b):
    if a == "Joshua":
        return True
    else:
        if b == "Joshua":
            return True
        else:
            return False

"""
2. The boy wearing the Black shirt is somewhere to the left of the youngest boy.
"""

def rule_two(a1, a2, a3, b1, b2, b3):
    # Split the string to get age number
    age1 = b1.split()
    age2 = b2.split()
    age3 = b3.split()

    # Convert strings to ints
    age_int = list()
    age_int.append(int(age1[0]))
    age_int.append(int(age2[0]))
    age_int.append(int(age3[0]))

    # Find min value
    minVal = min(age_int)
    minValS = str(minVal)
    minValSF = " ".join((minValS, "years"))

    if (b1 == minValSF and a1 == "black") or (b2 == minValSF and (a2 == "black" or a1 == "black")) or (
            b3 == minValSF and (a3 == "black" or a2 == "black" or a1 == "black")):
        return True
    else:
        return False


"""
3. Joshua likes Horror movies.
"""

def rule_three(a1, a2, a3, a4, b1, b2, b3, b4):
    if (a1 == "Joshua" and b1 == "horror") or (a2 == "Joshua" and b2 == "horror") or (
            a3 == "Joshua" and b3 == "horror") or (a4 == "Joshua" and b4 == "horror"):
        return True
    else:
        return False


"""
4. The 14-year-old boy is at the third position.
"""
def rule_four(a1, b1):
    if a1 == "14 years" and b1 == "Boy3":
        return True
    else:
        return False

"""
5. The boy wearing the Red shirt is somewhere between the 13-year-old boy and the one who likes Action movies, in that order.
"""

def rule_five(a1, a2, b1, b2, c3, c4):
    # ZConstraint(('p12','p13','p51','p52','p33','p34')
    if (b1 == "13 years" and a1 == "red" and c3 == "action") or (
            b1 == "13 years" and a2 == "red" and c4 == "action") or (
            b2 == "13 years" and a2 == "red" and c3 == "action") or (
            b1 == "13 years" and a1 == "red" and c3 == "action"):  # (5,1) (1,2) (3,4)
        return True
    else:
        return False

""""
6. Daniel likes Thriller movies.
"""

def rule_six(a1, a2, a3, a4, b1, b2, b3, b4):
    if (a1 == "Daniel" and b1 == "thriller") or (a2 == "Daniel" and b2 == "thriller") or (
            a3 == "Daniel" and b3 == "thriller") or (a4 == "Daniel" and b4 == "thriller"):
        return True
    else:
        return False

""""
7. The boy who is going to eat Cookies is in one of the ends.
"""
#def rule_seven(a1, a2, b1, b2):
#    if (a1 == "Boy1" and b1 == "cookies") or (a2 == "Boy4" and b2 == "cookies"):
#        return True
#    else:
#        return False
""""
8. The boy wearing the Black shirt is exactly to the left of the one who likes Thriller movies.
"""

def rule_eight(a1, a2, a3, b1, b2, b3):
    if (a1 == "black" and b1 == "thriller") or (a2 == "black" and b2 == "thriller") or (
            a3 == "black" and b3 == "thriller"):
        return True
    else:
        return False


""""
9. The boy who is going to eat Crackers is exactly to the right of the boy who likes Comedy movies.
"""

def rule_nine(a1, a2, a3, b1, b2, b3):
    if (a1 == "crackers" and b1 == "comedy") or (a2 == "crackers" and b2 == "comedy") or (
            a3 == "crackers" and b3 == "comedy"):
        return True
    else:
        return False

"""
10. The boy wearing the Red shirt is somewhere between the boy who is going to eat Popcorn and Nicholas, in that order.
"""

def rule_ten(a1, a2, b1, b2, c1, c2):
    if (a1 == "popcorn" and b1 == "red" and c1 == "Nicholas") or (
            a1 == "popcorn" and b2 == "red" and c2 == "Nicholas") or (
            a2 == "popcorn" and b2 == "red" and c2 == "Nicholas") or (
            a1 == "popcorn" and b1 == "red" and c2 == "Nicholas"):  # (4,1) (1,2) (2,4)
        return True
    else:
        return False

""""
11. In one of the ends is the boy who likes Thriller movies.
"""
def rule_eleven(a1, b1, a2, b2):
    if (a1 == "Boy1" and b1 == "thriller") or (a2 == "Boy4" and b2 == "thriller"):
        return True
    else:
        return False
""""
12. Nicholas is somewhere between Joshua and Daniel, in that order.
"""


def rule_twelve(a1, a2, a3, a4):
    if (a1 == "Joshua" and a2 == "Nicholas" and a3 == "Daniel") or (
            a1 == "Joshua" and a2 == "Nicholas" and a4 == "Daniel") or (
            a2 == "Joshua" and a3 == "Nicholas" and a4 == "Daniel") or (
            a1 == "Joshua" and a3 == "Nicholas" and a4 == "Daniel"):  # (2,1) (2,3) (2,4)
        return True
    else:
        return False


""""
13. At the first position is the boy wearing the Green shirt.
"""
def rule_thirteen(a1, b1):
    if a1 == "Boy1" and b1 == "green":
        return True
    else:
        return False

def solveZebraMovieNight():
    movie_night_csp = ZebraPuzzleCSP(
        {'p01': {'Boy1'}, 'p02': {'Boy2'}, 'p03': {'Boy3'}, 'p04': {'Boy4'}, 'p11': shirt, 'p12': shirt,
         'p13': shirt,
         'p14': shirt,
         'p21': name, 'p22': name, 'p23': name, 'p24': name,
         'p31': movie, 'p32': movie, 'p33': movie, 'p34': movie,
         'p41': snack, 'p42': snack, 'p43': snack, 'p44': snack,
         'p51': age, 'p52': age, 'p53': age, 'p54': age},
        [
            ZConstraint(('p11', 'p12', 'p13', 'p14'), notEqualSuper, "notEqualSuper(p11,p12,p13,p14)"),
            ZConstraint(('p21', 'p22', 'p23', 'p24'), notEqualSuper, "notEqualSuper(p21,p22,p23,p24)"),
            ZConstraint(('p31', 'p32', 'p33', 'p34'), notEqualSuper, "notEqualSuper(p31,p32,p33,p34)"),
            ZConstraint(('p41', 'p42', 'p43', 'p44'), notEqualSuper, "notEqualSuper(p41,p42,p43,p44)"),
            ZConstraint(('p51', 'p52', 'p53', 'p54'), notEqualSuper, "notEqualSuper(p51,p52,p53,p54)"),
            ZConstraint(('p21', 'p24'), rule_one, "rule_one(p21,p24)"),
            ZConstraint(('p11', 'p12', 'p13', 'p52', 'p53', 'p54'), rule_two, "rule_two(p11,p12,p13,p52,p53,p54)"),
            ZConstraint(('p21', 'p22', 'p23', 'p24', 'p31', 'p32', 'p33', 'p34'), rule_three, "rule_three(p21,p22,p23,p24,p31,p32,p33,p34)"),
            ZConstraint(('p53', 'p03'), rule_four, "rule_four(p53,p03)"),
            ZConstraint(('p12', 'p13', 'p51', 'p52', 'p33', 'p34'), rule_five,
                        "rule_five('p12','p13','p51','p52','p33','p34')"),
            ZConstraint(('p21', 'p22', 'p23', 'p24', 'p31', 'p32', 'p33', 'p34'), rule_six, "rule_six(p21,p22,p23,p24,p31,p32,p33,p34)"),
            ZConstraint(('p42',), ne_('cookies'), "p42 != 'cookies'"),
            ZConstraint(('p43',), ne_('cookies'), "p43 != 'cookies'"),
            ZConstraint(('p11', 'p12', 'p13', 'p32', 'p33', 'p34'), rule_eight, "rule_eight(p11,p12,p13,p32,p33,p34)"),
            ZConstraint(('p42', 'p43', 'p44', 'p31', 'p32', 'p33'), rule_nine, "rule_nine(p42,p43,p44,p31,p32,p33)"),
            ZConstraint(('p21', 'p22', 'p23', 'p24'), rule_twelve, "rule_twelve(p21,p22,p23,p24)"),
            ZConstraint(('p01', 'p31', 'p04', 'p34'), rule_eleven, "rule_eleven(p01,p31,p04,p34)"),
            ZConstraint(('p01', 'p11'), rule_thirteen, "rule_thirteen(p01,p11)"),
            ZConstraint(('p41', 'p42', 'p12', 'p13', 'p23', 'p24'), rule_ten, "rule_ten(p41,p42,p12,p13,p23,p24)")
        ])

    solution = ac_search_solver(movie_night_csp)
    finaldict = dict()
    finaldict[1] = []
    finaldict[2] = []
    finaldict[3] = []
    finaldict[4] = []

    global a
    a = list()
    b = list()
    c = list()
    d = list()

    for i in solution:
        if i[2] == '1':
            a.append(solution.get(i))
        elif i[2] == '2':
            b.append(solution.get(i))
        elif i[2] == '3':
            c.append(solution.get(i))
        elif i[2] == '4':
            d.append(solution.get(i))

    a.remove('Boy1')
    b.remove('Boy2')
    c.remove('Boy3')
    d.remove('Boy4')

    finaldict[1] = a
    finaldict[2] = b
    finaldict[3] = c
    finaldict[4] = d

    return finaldict


# ********PROBLEM #2: Zebra Puzzle - Einstein's Puzzle Problem *************

color = {'blue', 'green', 'red', 'white', 'yellow'}
nationality = {'Brit', 'Dane', 'German', 'Norwegian', 'Swede'}
drink = {'beer', 'coffee', 'milk', 'tea', 'water'}
cigarette = {'Blends', 'Blue Master', 'Dunhill', 'Pall Mall', 'Prince'}
pet = {'birds', 'cats', 'dogs', 'horses', 'fish'}


def notEqualSuper2(a, b, c, d, e):
    complist = list()
    complist.append(a)
    complist.append(b)
    complist.append(c)
    complist.append(d)
    complist.append(e)

    seen = set()
    for x in complist:
        if x in seen:
            return False
        seen.add(x)

    return True


"""
1. The Brit lives in the Red house.
"""


def rule_one_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    a = [a1, a2, a3, a4, a5]
    b = [b1, b2, b3, b4, b5]

    for i in range(len(a)):
        if (a[i] == "Brit" and b[i] == "red"):
            return True

    return False


"""    
2. The Swede keeps Dogs as pets.
"""


def rule_two_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    a = [a1, a2, a3, a4, a5]
    b = [b1, b2, b3, b4, b5]

    for i in range(len(a)):
        if (a[i] == "Swede" and b[i] == "dogs"):
            return True

    return False


"""
3. The Dane drinks Tea.
"""


def rule_three_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    a = [a1, a2, a3, a4, a5]
    b = [b1, b2, b3, b4, b5]

    for i in range(len(a)):
        if (a[i] == "Dane" and b[i] == "tea"):
            return True

    return False


"""
4. The Green house is exactly to the left of the Whitehouse.
"""


def rule_four_2(a1, a2, a3, a4, a5):
    a = [a1, a2, a3, a4, a5]

    for i in range(len(a) - 1):
        if (a[i] == "green" and a[i + 1] == "white"):
            return True

    return False


"""
5. The owner of the Green house drinks Coffee.
"""


def rule_five_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    a = [a1, a2, a3, a4, a5]
    b = [b1, b2, b3, b4, b5]

    for i in range(len(a)):
        if (a[i] == "green" and b[i] == "coffee"):
            return True

    return False


"""
6. The person who smokes Pall Mall rears Birds.
"""


def rule_six_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    a = [a1, a2, a3, a4, a5]
    b = [b1, b2, b3, b4, b5]

    for i in range(len(a)):
        if (a[i] == "Pall Mall" and b[i] == "birds"):
            return True

    return False


"""
7. The owner of the Yellow house smokes Dunhill.
"""


def rule_seven_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    a = [a1, a2, a3, a4, a5]
    b = [b1, b2, b3, b4, b5]

    for i in range(len(a)):
        if (a[i] == "Pall Mall" and b[i] == "yellow"):
            return True

    return False


"""
8. The man living in the centre house drinks Milk.
"""


def rule_eight_2(a1, b1):
    if a1 == "House3" and b1 == "milk":  # this set meets the criteria
        return True
    else:
        return False


"""
9. The Norwegian lives in the first house.
"""


def rule_nine_2(a1, b1):
    if a1 == "House1" and b1 == "Norwegian":  # this set meets the criteria
        return True
    else:
        return False


"""
10. The man who smokes Blends lives next to the one who keeps Cats.
"""


def rule_ten_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    a = [a1, a2, a3, a4, a2, a3, a4, a5]
    b = [b2, b3, b4, b5, b1, b2, b3, b4]

    for i in range(len(a)):
        if (a[i] == "Blends" and b[i] == "cats"):
            return True

    return False


"""
11. The man who keeps Horses lives next to the man who smokes Dunhill.
"""


def rule_eleven_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    a = [a1, a2, a3, a4, a2, a3, a4, a5]
    b = [b2, b3, b4, b5, b1, b2, b3, b4]

    for i in range(len(a)):
        if (a[i] == "Dunhill" and b[i] == "horses"):
            return True

    return False


"""
12. The man who smokes Blue Master drinks Beer.
"""


def rule_twelve_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    if (a1 == "Blue Master" and b1 == "beer") or (a2 == "Blue Master" and b2 == "beer") or (
            a3 == "Blue Master" and b3 == "beer") or (a4 == "Blue Master" and b4 == "beer") or (
            a5 == "Blue Master" and b5 == "beer"):
        return True
    else:
        return False


"""
13. The German smokes Prince.
"""


def rule_thirteen_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    if (a1 == "Prince" and b1 == "German") or (a2 == "Prince" and b2 == "German") or (
            a3 == "Prince" and b3 == "German") or (a4 == "Prince" and b4 == "German") or (
            a5 == "Prince" and b5 == "German"):
        return True
    else:
        return False


"""
14. The Norwegian lives next to the Blue house.
"""


def rule_fourteen_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    if (a1 == "Norwegian" and b2 == "blue") or (a2 == "Norwegian" and b3 == "blue") or (
            a3 == "Norwegian" and b4 == "blue") or (a4 == "Norwegian" and b5 == "blue") or (
            a2 == "Norwegian" and b1 == "blue") or (a3 == "Norwegian" and b2 == "blue") or (
            a4 == "Norwegian" and b3 == "blue") or (a5 == "Norwegian" and b4 == "blue"):
        return True
    else:
        return False


"""
15. The man who smokes Blends has a neighbour who drinks Water.
"""


def rule_fifteen_2(a1, a2, a3, a4, a5, b1, b2, b3, b4, b5):
    if (a1 == "Blends" and b2 == "water") or (a2 == "Blends" and b3 == "water") or (
            a3 == "Blends" and b4 == "water") or (a4 == "Blends" and b5 == "water") or (
            a2 == "Blends" and b1 == "water") or (a3 == "Blends" and b2 == "water") or (
            a4 == "Blends" and b3 == "water") or (a5 == "Blends" and b4 == "water"):
        return True
    else:
        return False


def solveZebraEinsteinRiddle():
    einsteins_riddle_csp = ZebraPuzzleCSP(
        {'p01': {'House1'}, 'p02': {'House2'}, 'p03': {'House3'}, 'p04': {'House4'}, 'p05': {'House5'}, 'p11': color,
         'p12': color, 'p13': color, 'p14': color, 'p15': color,
         'p21': nationality, 'p22': nationality, 'p23': nationality, 'p24': nationality, 'p25': nationality,
         'p31': drink, 'p32': drink, 'p33': drink, 'p34': drink, 'p35': drink,
         'p41': cigarette, 'p42': cigarette, 'p43': cigarette, 'p44': cigarette, 'p45': cigarette,
         'p51': pet, 'p52': pet, 'p53': pet, 'p54': pet, 'p55': pet},
        [
            ZConstraint(('p11', 'p12', 'p13', 'p14', 'p15'), notEqualSuper2, "notEqualSuper2(p11,p12,p13,p14,p15)"),
            ZConstraint(('p21', 'p22', 'p23', 'p24', 'p25'), notEqualSuper2, "notEqualSuper2(p21,p22,p23,p24,p25)"),
            ZConstraint(('p31', 'p32', 'p33', 'p34', 'p35'), notEqualSuper2, "notEqualSuper2(p31,p32,p33,p34,p35)"),
            ZConstraint(('p41', 'p42', 'p43', 'p44', 'p45'), notEqualSuper2, "notEqualSuper2(p41,p42,p43,p44,p45)"),
            ZConstraint(('p51', 'p52', 'p53', 'p54', 'p55'), notEqualSuper2, "notEqualSuper2(p51,p52,p53,p54,p55)"),
            ZConstraint(('p21', 'p22', 'p23', 'p24', 'p25', 'p11', 'p12', 'p13', 'p14', 'p15'), rule_one_2,
                        "rule_one_2(p21,p22,p23,p24,p25,p11,p12,p13,p14,p15)"),
            ZConstraint(('p21', 'p22', 'p23', 'p24', 'p25', 'p51', 'p52', 'p53', 'p54', 'p55'), rule_two_2,
                        "rule_two_2(p21,p22,p23,p24,p25,p51,p52,p53,p54,p55)"),
            ZConstraint(('p21', 'p22', 'p23', 'p24', 'p25', 'p31', 'p32', 'p33', 'p34', 'p35'), rule_three_2,
                        "rule_three_2(p21,p22,p23,p24,p25,p31,p32,p33,p34,p35)"),
            ZConstraint(('p11', 'p12', 'p13', 'p14', 'p15'), rule_four_2, "rule_four_2(p11,p12,p13,p14,p15,)"),
            ZConstraint(('p11', 'p12', 'p13', 'p14', 'p15', 'p31', 'p32', 'p33', 'p34', 'p35'), rule_five_2,
                        "rule_five_2(p11,p12,p13,p14,p15,p31,p32,p33,p34,p35)"),
            ZConstraint(('p41', 'p42', 'p43', 'p44', 'p45', 'p51', 'p52', 'p53', 'p54', 'p55'), rule_six_2,
                        "rule_six_2(p41,p42,p43,p44,p45,p51,p52,p53,p54,p55)"),
            ZConstraint(('p41', 'p42', 'p43', 'p44', 'p45', 'p11', 'p12', 'p13', 'p14', 'p15'), rule_seven_2,
                        "rule_seven_2(p41,p42,p43,p44,p45,p11,p12,p13,p14,p15)"),
            ZConstraint(('p03', 'p33'), rule_eight_2, "rule_eight_2(p03,p33)"),
            ZConstraint(('p01', 'p21'), rule_nine_2, "rule_nine_2(p01,p21)"),
            ZConstraint(('p41', 'p42', 'p43', 'p44', 'p45', 'p51', 'p52', 'p53', 'p54', 'p55'), rule_ten_2,
                        "rule_ten_2(p41,p42,p43,p44,p45,p51,p52,p53,p54,p55)"),
            ZConstraint(('p41', 'p42', 'p43', 'p44', 'p45', 'p51', 'p52', 'p53', 'p54', 'p55'), rule_eleven_2,
                        "rule_eleven_2(p41,p42,p43,p44,p45,p51,p52,p53,p54,p55)"),
            ZConstraint(('p41', 'p42', 'p43', 'p44', 'p45', 'p31', 'p32', 'p33', 'p34', 'p35'), rule_twelve_2,
                        "rule_twelve_2(p41,p42,p43,p44,p45,p31,p32,p33,p34,p35)"),
            ZConstraint(('p41', 'p42', 'p43', 'p44', 'p45', 'p21', 'p22', 'p23', 'p24', 'p25'), rule_thirteen_2,
                        "rule_thirteen_2(p41,p42,p43,p44,p45,p21,p22,p23,p24,p25)"),
            ZConstraint(('p21', 'p22', 'p23', 'p24', 'p25', 'p11', 'p12', 'p13', 'p14', 'p15'), rule_fourteen_2,
                        "rule_fourteen_2(p21,p22,p23,p24,p25,p11,p12,p13,p14,p15)"),
            ZConstraint(('p41', 'p42', 'p43', 'p44', 'p45', 'p31', 'p32', 'p33', 'p34', 'p35'), rule_fifteen_2,
                        "rule_thirteen_2(p41,p42,p43,p44,p45,p31,p32,p33,p34,p35)")
        ])

    solution = ac_search_solver(einsteins_riddle_csp)
    finaldict = dict()
    finaldict[1] = []
    finaldict[2] = []
    finaldict[3] = []
    finaldict[4] = []
    finaldict[5] = []

    global a
    a = list()
    b = list()
    c = list()
    d = list()
    e = list()

    for i in solution:
        if i[2] == '1':
            a.append(solution.get(i))
        elif i[2] == '2':
            b.append(solution.get(i))
        elif i[2] == '3':
            c.append(solution.get(i))
        elif i[2] == '4':
            d.append(solution.get(i))
        elif i[2] == '5':
            e.append(solution.get(i))

    a.remove('House1')
    b.remove('House2')
    c.remove('House3')
    d.remove('House4')
    e.remove('House5')

    finaldict[1] = a
    finaldict[2] = b
    finaldict[3] = c
    finaldict[4] = d
    finaldict[5] = e

    return finaldict


# ********PROBLEM #3: Cryptoarithmic Problem *************

class ZConstraint(object):
    """A Constraint consists of
    * scope: a tuple of variables
    * condition: a function that can applied to a tuple of values
    * string: a string for printing the constraints. All of the strings must be unique.
    for the variables
    """

    def __init__(self, scope, condition, string=None):
        self.scope = scope
        self.condition = condition
        if string is None:
            self.string = self.condition.__name__ + str(self.scope)
        else:
            self.string = string

    def __repr__(self):
        return self.string

    def holds(self, assignment):
        """returns the value of Constraint con evaluated in assignment.

        precondition: all variables are assigned in assignment
        """
        return self.condition(*tuple(assignment[v] for v in self.scope))


class ZebraPuzzleCSP(object):
    """A CSP consists of
        * domains, a dictionary that maps each variable to its domain
        * constraints, a list of constraints
        * variables, a set of variables
        * var_to_const, a variable to set of constraints dictionary
        """

    def __init__(self, domains, constraints, positions={}):
        """domains is a variable:domain dictionary
        constraints is a list of constriants
        """
        self.variables = set(domains)
        self.domains = domains
        self.constraints = constraints
        self.positions = positions
        self.var_to_const = {var: set() for var in self.variables}
        for con in constraints:
            for var in con.scope:
                self.var_to_const[var].add(con)

    def __str__(self):
        """string representation of CSP"""
        return str(self.domains)

    def getDom(self):
        return self.domains

    def __repr__(self):
        """more detailed string representation of CSP"""
        return "CSP(" + str(self.domains) + ", " + str([str(c) for c in self.constraints]) + ")"

    def consistent(self, assignment):
        """assignment is a variable:value dictionary
        returns True if all of the constraints that can be evaluated
                        evaluate to True given assignment.
        """
        return all(con.holds(assignment)
                   for con in self.constraints
                   if all(v in assignment for v in con.scope))


def notEqualSuper3(a, b, c, d, e, f):
    complist = list()
    complist.append(a)
    complist.append(b)
    complist.append(c)
    complist.append(d)
    complist.append(e)
    complist.append(f)

    seen = set()
    for x in complist:
        if x in seen:
            return False
        seen.add(x)

    return True


def notEqualSuper4(a, b, c, d, e, f, g, h):
    complist = list()
    complist.append(a)
    complist.append(b)
    complist.append(c)
    complist.append(d)
    complist.append(e)
    complist.append(f)
    complist.append(g)
    complist.append(h)

    seen = set()
    for x in complist:
        if x in seen:
            return False
        seen.add(x)

    return True


def carryEqual(a, b):
    if a == b:
        return True
    else:
        return False


def notEqualZero(a, b):
    if a != 0:
        return True
    else:
        return False


def cryptAdd(a, b, c):
    sum1 = a + a
    sum2 = b + 10 * c

    if sum1 == sum2:
        return True
    else:
        return False


def cryptAdd2(a, b, c, d):
    sum1 = a + b
    sum2 = c + 10 * d

    if sum1 == sum2:
        return True
    else:
        return False


def cryptAdd3(a, b, c, d, e):
    sum1 = a + b + e
    sum2 = c + 10 * d

    if sum1 == sum2:
        return True
    else:
        return False

"""
TWO + TWO = FOUR
"""

def solveTwoTwoFour():
    crypto1_csp = ZebraPuzzleCSP(
        {'T': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'W': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'O': {0, 1,2, 3, 4, 5, 6, 7, 8, 9},
         'F': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'U': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'R': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
         'C1': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'C2': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
         'C3': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}},
        [
            ZConstraint(('T', 'W', 'O', 'F', 'U', 'R'), notEqualSuper3, "notEqualSuper3(T,W,O,F,U,R)"),
            ZConstraint(('O', 'O', 'R', 'C1'), cryptAdd2, "cryptAdd1(O,O,R,C1)"),
            ZConstraint(('W', 'W', 'U', 'C2', 'C1'), cryptAdd3, "cryptAdd1(W,U,C2,C1)"),
            ZConstraint(('T', 'T', 'O', 'C3', 'C2'), cryptAdd3, "cryptAdd1(T,O,C3,C2)"),
            ZConstraint(('T', 'T'), notEqualZero, "notEqualZero(T,T)"),
            ZConstraint(('F', 'F'), notEqualZero, "notEqualZero(F,F)"),
            ZConstraint(('F', 'C3'), carryEqual, "carryEqual(F,C3)")])

    sol = ac_search_solver(crypto1_csp)
    return sol

"""
SEND + MORE = MONEY
"""

def solveSendMoreMoney():
    crypto2_csp = ZebraPuzzleCSP(
        {'S': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'E': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'N': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
         'D': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'M': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'O': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
         'R': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'Y': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'C1': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
         'C2': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'C3': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
         'C4': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}},
        [
            ZConstraint(('S', 'E', 'N', 'D', 'M', 'O', 'R', 'Y'), notEqualSuper4, "notEqualSuper4(S,E,N,D,M,O,R,Y)"),
            ZConstraint(('D', 'E', 'Y', 'C1'), cryptAdd2, "cryptAdd2(D,E,Y,C1)"),
            ZConstraint(('N', 'R', 'E', 'C2', 'C1'), cryptAdd3, "cryptAdd3(N,R,E,C2,C1)"),
            ZConstraint(('E', 'O', 'N', 'C3', 'C2'), cryptAdd3, "cryptAdd3(E,O,N,C3,C2)"),
            ZConstraint(('S', 'M', 'O', 'C4', 'C3'), cryptAdd3, "cryptAdd3(S,M,O,C4,C3)"),
            ZConstraint(('S', 'S'), notEqualZero, "notEqualZero(S,S)"),
            ZConstraint(('M', 'M'), notEqualZero, "notEqualZero(M,M)"),
            ZConstraint(('M', 'C4'), carryEqual, "carryEqual(M,C4)")])

    sol = ac_search_solver(crypto2_csp)
    return sol


# ********PROBLEM #4: NQueens Problem *************

def createVar(n):
    finalDict = dict()

    a = list()
    dom = set()
    for k in range(n):
        for d in range(n):
            dom.add((k, d))

    for i in range(n):
        a.append("Queens" + str(i))

    for p in range(n):
        finalDict[a[p]] = dom

    return finalDict


def QConstraint1(a, b):
    rows_apart = abs(a[0] - b[0])
    cols_apart = abs(a[1] - b[1])

    if (a == b) or (a[1] == b[1]) or (a[0] == b[0]) or (rows_apart == cols_apart):
        return False
    else:
        return True


import itertools


def createVar1(n):
    finalSet = set()
    finalDict = dict()

    a = list()
    dom = set()
    for k in range(n):
        for d in range(n):
            dom.add((k, d))

    for i in range(n):
        a.append("Queens" + str(i))

    for p in range(n):
        finalDict[a[p]] = dom

    return finalDict


def createDom(n):
    dom = set()
    for k in range(n):
        for d in range(n):
            dom.add((k, d))
    return dom


def qConstraint1_2(a, b):
    rows_apart = abs(a[0] - b[0])
    cols_apart = abs(a[1] - b[1])

    if (str(a) == str(b)) or (rows_apart == cols_apart):
        return False
    else:
        return True


def solveNQueens(n: int):
    solution = ac_search_solver(NQueensColoringCSP(createVar1(n), createDom(n), n))
    solList = list()

    for i in range(n):
        solList.append(solution.get("Queens" + str(i)))

    return solList

# neighbors = """SA: WA NT Q NSW V; NT: WA Q; NSW: Q V; T: """
# colors = list('RGB')

# print(solveMapColoringCSP(colors, neighbors))
# print(solveNQueens(4))
# print(solveSendMoreMoney())
# print(solveTwoTwoFour())
# print(solveZebraBasic())
# print(solveZebraMovieNight())
# print(solveZebraEinsteinRiddle())