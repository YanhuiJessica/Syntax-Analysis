from FiniteAutomata import *
from LR import *

def syntaxAnalysis(lr_struct):
    while True:
        try:
            s = input('Please input a sentence to analysis: ')
            if lr_struct.Analysis(s):
                print('Accepted')
            else:
                print('Unaccepted')
        except EOFError:
            break

if __name__ == '__main__':
    # using example
    # syntax-demo.txt no new line at the end of file
    f = open('syntax-demo.txt', 'r', encoding = 'UTF-8')

    a = LR()
    a.scan(f)   # read the file
    a.BuildSimpleDFA()
    if a.BuildLR0AnalyseTable():
        a.dfa.displaySimpleSquare('simpledfa.gv', 'simple_dfa', a.projectSet)
        syntaxAnalysis(a)
    elif a.BuildSLR1AnalyseTable():
        syntaxAnalysis(a)
    else:
        a.BuildDFA()
        a.dfa.displaySquare('dfa.gv', 'dfa_with_lookahead', a.projectSet, a.LATerminal)
        if a.BuildLR1AnalyseTable():
            syntaxAnalysis(a)