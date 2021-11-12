# cspExamples.py - Example CSPs
# AIFCA Python3 code Version 0.8.2 Documentation at http://aipython.org

# Artificial Intelligence: Foundations of Computational Agents
# http://artint.info
# Copyright David L Poole and Alan K Mackworth 2017.
# This work is licensed under a Creative Commons
# Attribution-NonCommercial-ShareAlike 4.0 International License.
# See: http://creativecommons.org/licenses/by-nc-sa/4.0/deed.en

from cspProblem import CSP, Constraint, ZConstraint, MapColoringCSP, ZebraPuzzleCSP
from operator import lt, ne, eq, gt

def ne_(val):
    """not equal value"""

    # nev = lambda x: x != val   # alternative definition
    # nev = partial(neq,val)     # another alternative definition
    def nev(x):
        return val != x

    nev.__name__ = str(val) + "!="  # name of the function
    return nev


def is_(val):
    """is a value"""

    # isv = lambda x: x == val   # alternative definition
    # isv = partial(eq,val)      # another alternative definition
    def isv(x):
        return val == x

    isv.__name__ = str(val) + "=="
    return isv


csp0 = CSP({'X': {1, 2, 3}, 'Y': {1, 2, 3}, 'Z': {1, 2, 3}},
           [Constraint(('X', 'Y'), lt),
            Constraint(('Y', 'Z'), lt)])

C0 = Constraint(('A', 'B'), lt, "A < B")
C1 = Constraint(('B',), ne_(2), "B != 2")
C2 = Constraint(('B', 'C'), lt, "B < C")
csp1 = CSP({'A': {1, 2, 3, 4}, 'B': {1, 2, 3, 4}, 'C': {1, 2, 3, 4}},
           [C0, C1, C2],
           positions={"A": (1, 0),
                      "B": (3, 0),
                      "C": (5, 0),
                      "A < B": (2, 1),
                      "B < C": (4, 1),
                      "B != 2": (3, 2)})

csp2 = CSP({'A': {1, 2, 3, 4}, 'B': {1, 2, 3, 4}, 'C': {1, 2, 3, 4},
            'D': {1, 2, 3, 4}, 'E': {1, 2, 3, 4}},
           [Constraint(('B',), ne_(3), "B != 3"),
            Constraint(('C',), ne_(2), "C != 2"),
            Constraint(('A', 'B'), ne, "A != B"),
            Constraint(('B', 'C'), ne, "A != C"),
            Constraint(('C', 'D'), lt, "C < D"),
            Constraint(('A', 'D'), eq, "A = D"),
            Constraint(('A', 'E'), gt, "A > E"),
            Constraint(('B', 'E'), gt, "B > E"),
            Constraint(('C', 'E'), gt, "C > E"),
            Constraint(('D', 'E'), gt, "D > E"),
            Constraint(('B', 'D'), ne, "B != D")])

csp3 = CSP({'A': {1, 2, 3, 4}, 'B': {1, 2, 3, 4}, 'C': {1, 2, 3, 4},
            'D': {1, 2, 3, 4}, 'E': {1, 2, 3, 4}},
           [Constraint(('A', 'B'), ne, "A != B"),
            Constraint(('A', 'D'), lt, "A < D"),
            Constraint(('A', 'E'), lambda a, e: (a - e) % 2 == 1, "A-E is odd"),  # A-E is odd
            Constraint(('B', 'E'), lt, "B < E"),
            Constraint(('D', 'C'), lt, "D < C"),
            Constraint(('C', 'E'), ne, "C != E"),
            Constraint(('D', 'E'), ne, "D != E")])

# ********PROBLEM #3: Cryptoarithmic Problem *************

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
crypto1_csp = ZebraPuzzleCSP(
    {'T': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'W': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'O': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
     'F': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'U': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'R': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
     'C1': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'C2': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
     'C3': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}},
    [
        ZConstraint(('T', 'W', 'O', 'F', 'U', 'R'), notEqualSuper3, "notEqualSuper3(T,W,O,F,U,R)"),
        ZConstraint(('O', 'O', 'R', 'C1'), cryptAdd2, "cryptAdd1(O,O,R,C1)"),
        ZConstraint(('W', 'W', 'U', 'C2', 'C1'), cryptAdd3, "cryptAdd1(W,U,C2,C1)"),
        ZConstraint(('T', 'T', 'O', 'C3', 'C2'), cryptAdd3, "cryptAdd1(T,O,C3,C2)"),
        ZConstraint(('T', 'T'), notEqualZero, "notEqualZero(T,T)"),
        ZConstraint(('F', 'C3'), carryEqual, "carryEqual(F,C3)")])

"""
SEND + MORE = MONEY
"""
crypto2_csp = ZebraPuzzleCSP(
    {'S': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'E': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'N': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
     'D': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'M': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'O': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
     'R': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'Y': {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}, 'C1': {0, 1},
     'C2': {0, 1}, 'C3': {0, 1}, 'C4': {0, 1}},
    [
        ZConstraint(('S', 'E', 'N', 'D', 'M', 'O', 'R', 'Y'), notEqualSuper4, "notEqualSuper4(S,E,N,D,M,O,R,Y)"),
        ZConstraint(('D', 'E', 'Y', 'C1'), cryptAdd2, "cryptAdd2(D,E,Y,C1)"),
        ZConstraint(('N', 'R', 'E', 'C2', 'C1'), cryptAdd3, "cryptAdd3(N,R,E,C2,C1)"),
        ZConstraint(('E', 'O', 'N', 'C3', 'C2'), cryptAdd3, "cryptAdd3(E,O,N,C3,C2)"),
        ZConstraint(('S', 'M', 'O', 'C4', 'C3'), cryptAdd3, "cryptAdd3(S,M,O,C4,C3)"),
        ZConstraint(('S', 'S'), notEqualZero, "notEqualZero(S,S)"),
        ZConstraint(('M', 'M'), notEqualZero, "notEqualZero(M,M)"),
        ZConstraint(('M', 'C4'), carryEqual, "carryEqual(M,C4)")])

# ************ END PROBLEMS ********************

def adjacent(x, y):
    """True when x and y are adjacent numbers"""
    return abs(x - y) == 1


csp4 = CSP({'A': {1, 2, 3, 4, 5}, 'B': {1, 2, 3, 4, 5}, 'C': {1, 2, 3, 4, 5},
            'D': {1, 2, 3, 4, 5}, 'E': {1, 2, 3, 4, 5}},
           [Constraint(('A', 'B'), adjacent, "adjacent(A,B)"),
            Constraint(('B', 'C'), adjacent, "adjacent(B,C)"),
            Constraint(('C', 'D'), adjacent, "adjacent(C,D)"),
            Constraint(('D', 'E'), adjacent, "adjacent(D,E)"),
            Constraint(('A', 'C'), ne, "A != C"),
            Constraint(('B', 'D'), ne, "A != D"),
            Constraint(('C', 'E'), ne, "C != E")])


def meet_at(p1, p2):
    """returns a function of two words that is true when the words intersect at postions p1, p2.
    The positions are relative to the words; starting at position 0.
    meet_at(p1,p2)(w1,w2) is true if the same letter is at position p1 of word w1
         and at position p2 of word w2.
    """

    def meets(w1, w2):
        return w1[p1] == w2[p2]

    meets.__name__ = "meet_at(" + str(p1) + ',' + str(p2) + ')'
    return meets


crossword1 = CSP({'one_across': {'ant', 'big', 'bus', 'car', 'has'},
                  'one_down': {'book', 'buys', 'hold', 'lane', 'year'},
                  'two_down': {'ginger', 'search', 'symbol', 'syntax'},
                  'three_across': {'book', 'buys', 'hold', 'land', 'year'},
                  'four_across': {'ant', 'big', 'bus', 'car', 'has'}},
                 [Constraint(('one_across', 'one_down'), meet_at(0, 0)),
                  Constraint(('one_across', 'two_down'), meet_at(2, 0)),
                  Constraint(('three_across', 'two_down'), meet_at(2, 2)),
                  Constraint(('three_across', 'one_down'), meet_at(0, 2)),
                  Constraint(('four_across', 'two_down'), meet_at(0, 4))])

words = {'ant', 'big', 'bus', 'car', 'has', 'book', 'buys', 'hold',
         'lane', 'year', 'ginger', 'search', 'symbol', 'syntax'}


def is_word(*letters, words=words):
    """is true if the letters concatenated form a word in words"""
    return "".join(letters) in words


letters = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l",
           "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y",
           "z"]

crossword1d = CSP({'p00': letters, 'p10': letters, 'p20': letters,  # first row
                   'p01': letters, 'p21': letters,  # second row
                   'p02': letters, 'p12': letters, 'p22': letters, 'p32': letters,  # third row
                   'p03': letters, 'p23': letters,  # fourth row
                   'p24': letters, 'p34': letters, 'p44': letters,  # fifth row
                   'p25': letters  # sixth row
                   },
                  [Constraint(('p00', 'p10', 'p20'), is_word),  # 1-across
                   Constraint(('p00', 'p01', 'p02', 'p03'), is_word),  # 1-down
                   Constraint(('p02', 'p12', 'p22', 'p32'), is_word),  # 3-across
                   Constraint(('p20', 'p21', 'p22', 'p23', 'p24', 'p25'), is_word),  # 2-down
                   Constraint(('p24', 'p34', 'p44'), is_word)  # 4-across
                   ])

def test(CSP_solver, csp=csp1, solutions=[{'A': 1, 'B': 3, 'C': 4}, {'A': 2, 'B': 3, 'C': 4}]):
    """CSP_solver is a solver that takes a csp and returns a solution
    csp is a constraint satisfaction problem
    solutions is the list of all solutions to csp
    This tests whether the solution returned by CSP_solver is a solution.
    """
    #print("Testing csp with", CSP_solver.__doc__)
    #sol0 = CSP_solver(csp)
    #print("Solution found:", sol0)
    # sol0 = CSP_solver(zebra_csp)
    # sol0 = CSP_solver(movie_night_csp)
    # print("Solution found:", sol0)
    # for key, value in sol0.items():
    #    print(key, ' : ', value)
    #assert sol0 in solutions, "Solution not correct for " + str(csp)
    # print("Passed unit test")
    #australia_csp
    #print(solveNQueens(10))
    #sol0 = CSP_solver(crypto1_csp)
    #sol1 = CSP_solver(crypto2_csp)
    #print(sol0)
    #print(sol1)
