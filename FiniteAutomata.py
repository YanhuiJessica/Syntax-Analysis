from graphviz import Digraph, render
from collections import defaultdict

Upper = [chr(i) for i in range(ord('A'), ord('Z') + 1)]
epsilon = 'ε'
dot = '·'
arrow = '→'

class FA:

    def __init__(self, symbol = set([])):
        self.states = set()
        self.symbol = symbol    # input symbol 输入符号表
        self.transitions = defaultdict(defaultdict)
        self.startstate = None

    def setStart(self, state):
        self.startstate = state
        self.states.add(state)

    def addSymbol(self, sy):
        if sy not in Upper:
            self.symbol.add(sy)

    def addTransition(self, fromstate, tostate, inputch):
        if isinstance(inputch, str):
            inputch = set([inputch])
        self.states.add(fromstate)
        self.states.add(tostate)
        if fromstate in self.transitions and tostate in self.transitions[fromstate]:
            self.transitions[fromstate][tostate] = \
            self.transitions[fromstate][tostate].union(inputch)
        else:
            self.transitions[fromstate][tostate] = inputch