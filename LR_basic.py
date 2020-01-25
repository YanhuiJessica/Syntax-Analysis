from collections import defaultdict
from FiniteAutomata import *

class LR:
    def __init__(self):
        self.projects = defaultdict(defaultdict)  # e.g. 1. S' -> ·S: projects[S'][·S] = 1 记录所有项目及编号
        self.sorted_projects = dict()   # e.g. 1. S' -> ·S: sorted_projects[1] = (S', ·S) 根据编号查找项目
        self.projectSet = dict()    # 项目集
        self.production = []    # 产生式

        # e.g. 3. A -> ·aA, 1. A -> aA: production_numdict[A][·aA] = 1  项目对应的产生式编号
        self.production_numdict = defaultdict(defaultdict)

        self.dfa = FA()
        self.projects_num = 0
        self.startsymbol = None
        self.nonterminals = []

    def setStart(self, startsy):
        self.startsymbol = startsy
        self.nonterminals.append(startsy)

    def addNonterminals(self, symbol):
        if symbol in Upper:
            if symbol not in self.nonterminals:
                self.nonterminals.append(symbol)
            return True
        return False

    def addProjects(self, fromexp, toexp):
        tmp = ''
        for ch in toexp:
            if ch != epsilon:
                tmp += ch
        toexp = tmp
        for cut in range(0, len(toexp) + 1):
            tmp = toexp[:cut] + dot + toexp[cut:]
            self.projects_num += 1
            self.production_numdict[fromexp][tmp] = len(self.production)
            self.projects[fromexp][tmp] = self.projects_num
            self.sorted_projects[self.projects_num] = (fromexp, tmp)
        self.production.append((fromexp, toexp))

    def scan(self, filetxt):
        lines = filetxt.readlines()
        if lines[0][0] not in Upper:
            return False
        self.setStart('S\'')
        self.addProjects('S\'', lines[0][0]) # add augmented grammar 添加拓广文法
        self.projectSet[0] = {(self.startsymbol, dot + lines[0][0])}
        for line in lines:
            if not self.addNonterminals(line[0]):
                return False
            if '\n' in line:
                line = line[:-1]
            fromexp = line[0]
            tmp = ''
            for s in line[3:]:
                if s == '|':
                    self.addProjects(fromexp, tmp)
                    tmp = ''
                    continue
                tmp += s
                self.dfa.addSymbol(s)
            self.addProjects(fromexp, tmp)