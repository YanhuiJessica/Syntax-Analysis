from graphviz import Digraph, render
from collections import defaultdict

Upper = [chr(i) for i in range(ord('A'), ord('Z') + 1)]
epsilon = 'ε'
dot = '·'
arrow = '→'
comma = ','

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

    def displaySimpleSquare(self, fname, pname, pst):   # do not contain lookahead terminals
        fa = Digraph(pname, filename = fname, format = 'png')
        fa.attr(rankdir='LR')

        fa.attr('node', shape = 'record')
        for fromstate, tostates in self.transitions.items():
            for state in tostates:
                fromstr = 'I' + str(fromstate) + ': '
                for pj in pst[fromstate]:
                    fromstr += pj[0] + arrow + pj[1] + '\\n'
                tostr = 'I' + str(state) + ': '
                for pj in pst[state]:
                    tostr += pj[0] + arrow + pj[1] + '\\n'
                fa.node('I' + str(fromstate), label = fromstr)
                fa.node('I' + str(state), label = tostr)
                fa.edge('I' + str(fromstate), 'I' + str(state), label = list(tostates[state])[0])

        fa.attr('node', shape = 'point')
        fa.edge('', 'I0')

        fa.view()

    def displaySquare(self, fname, pname, pst, LATerminal):
        fa = Digraph(pname, filename = fname, format = 'png')
        fa.attr(rankdir='LR')

        fa.attr('node', shape = 'record')
        for fromstate, tostates in self.transitions.items():
            for state in tostates:
                fromstr = 'I' + str(fromstate) + ': '
                for pj in pst[fromstate]:
                    tmp = ' '
                    for sy in LATerminal[fromstate][pj]:
                        tmp += sy + '|'
                    fromstr += pj[0] + arrow + pj[1] + comma + tmp[:-1] + '\\n'
                tostr = 'I' + str(state) + ': '
                for pj in pst[state]:
                    tmp = ' '
                    for sy in LATerminal[state][pj]:
                        tmp += sy + '|'
                    tostr += pj[0] + arrow + pj[1] + comma + tmp[:-1] + '\\n'
                fa.node('I' + str(fromstate), label = fromstr)
                fa.node('I' + str(state), label = tostr)
                fa.edge('I' + str(fromstate), 'I' + str(state), label = list(tostates[state])[0])