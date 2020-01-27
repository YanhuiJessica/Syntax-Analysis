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

    def getClosure(self, fromexp):
        pst = set()
        for toexp in self.projects[fromexp]:
            if toexp.find(dot) == 0:
                pst.add((fromexp, toexp))
        return pst

    def getProjectSet(self, pst):   # 获得整个项目集
        vis = set()
        while len(vis) != len(pst):
            for pj in pst:
                if pj in vis:
                    continue
                vis.add(pj)
                nxtpos = pj[1].find(dot) + 1
                if nxtpos == len(pj[1]) or pj[1][nxtpos] not in Upper:
                    continue
                pst = pst.union(self.getClosure(pj[1][nxtpos]))
        return pst

     def getNxtStateId(self, fromst, sy): # get next project set id 根据当前项目集编号和获得符号获得下一个项目集编号
        if fromst not in self.sy2stat or sy not in self.sy2stat[fromst]:
            self.projectset_num += 1
            self.sy2stat[fromst][sy] = self.projectset_num
            stnum = self.projectset_num
        else:
            return self.sy2stat[fromst][sy], False
        return stnum, True

    def addProjectSet(self, Iid, project):
        if isinstance(project, tuple):
            project = set([project])
        if Iid in self.projectSet:
            self.projectSet[Iid] = self.projectSet[Iid].union(project)
        else:
            self.projectSet[Iid] = project

    def BuildSimpleDFA(self):   # do not contain lookahead terminals
        self.sy2stat = defaultdict(defaultdict) # sy2stat[next_project_set_i_id][get_one_symbol] = next_project_set_j_id
        self.projectset_num = 0
        self.dfa.setStart(0)
        q = [0]
        while len(q):
            Iid = q.pop()
            self.projectSet[Iid] = self.getProjectSet(self.projectSet[Iid])
            tmpdict = dict()    # get one symbol and move to next project set, tmpdict[symbol] = next_project_set
            for pj in self.projectSet[Iid]:
                nxtpos = pj[1].find(dot) + 1
                if nxtpos == len(pj[1]):
                    continue
                nxtsy = pj[1][nxtpos]
                nxtpj = pj[1][:nxtpos - 1] + nxtsy + dot + pj[1][nxtpos + 1: ]  # moving dot behind next symbol 将·后移一个符号
                if nxtsy in tmpdict:
                    tmpdict[nxtsy].add((pj[0], nxtpj))
                else:
                    tmpdict[nxtsy] = set([(pj[0], nxtpj)])

            for nxtsy in tmpdict:
                tmpdict[nxtsy] = self.getProjectSet(tmpdict[nxtsy])
                if tmpdict[nxtsy] in self.projectSet.values():
                    self.sy2stat[Iid][nxtsy] = list(self.projectSet.keys())[list(self.projectSet.values()).index(tmpdict[nxtsy])]
                    continue
                nxtIid, flag = self.getNxtStateId(Iid, nxtsy)
                if flag:
                    q.append(nxtIid)
                self.addProjectSet(nxtIid, tmpdict[nxtsy])
                self.dfa.addTransition(Iid, nxtIid, nxtsy)