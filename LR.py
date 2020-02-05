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

    def addAction(self, stateid, sy, operation):
        if isinstance(operation, str):
            operation = set([operation])
        if stateid in self.action and sy in self.action[stateid]:
            self.action[stateid][sy] = self.action[stateid][sy].union(operation)
        else:
            self.action[stateid][sy] = operation

    def addGoto(self, stateid, sy, operation):
        if isinstance(operation, int):
            operation = set([operation])
        if stateid in self.goto and sy in self.goto[stateid]:
            self.goto[stateid][sy] = self.goto[stateid][sy].union(operation)
        else:
            self.goto[stateid][sy] = operation

    def GO(self, state, sy):
        return self.sy2stat[state][sy]

    def BuildLR0AnalyseTable(self):
        self.action = defaultdict(defaultdict)
        self.goto = defaultdict(defaultdict)
        for Iid in self.projectSet:
            for pj in self.projectSet[Iid]:
                nxtpos = pj[1].find(dot) + 1
                if nxtpos == len(pj[1]):
                    if self.projects[pj[0]][pj[1]] == 2:
                        self.addAction(Iid, '#', 'acc')
                    else:
                        op = 'r' + str(self.production_numdict[pj[0]][pj[1]])
                    if self.production_numdict[pj[0]][pj[1]] == 0:
                        continue
                    self.addAction(Iid, '#', op)
                    for sy in self.dfa.symbol:
                        self.addAction(Iid, sy, op)
                    continue
                nxtsy = pj[1][nxtpos]
                op = 'S' + str(self.GO(Iid, nxtsy))
                if nxtsy not in Upper:
                    self.addAction(Iid, nxtsy, op)
                else:
                    self.addGoto(Iid, nxtsy, int(op[1:]))

        for stat in self.action:
            for sy in self.action[stat]:
                if len(self.action[stat][sy]) > 1:
                    print("It's not a LR(0) grammer.")
                    return False
        print("It's a LR(0) grammer.")
        return True

    def addFirst(self, nt, sy):
        if isinstance(sy, str):
            sy = set([sy])
        if nt in self.First:
            self.First[nt] = self.First[nt].union(sy)
        else:
            self.First[nt] = sy

    def getFirst(self, nt):
        if nt in self.First:
            return self.First[nt]
        for pro in self.production:
            if len(pro[1]) == 0:
                continue
            if pro[0] == nt:
                if pro[1][0] not in Upper:
                    self.addFirst(nt, pro[1][0])
                else:
                    if len(pro[1]) == 1:
                        self.addFirst(nt, self.getFirst(pro[1]))
                    else:
                        l = len(pro[1])
                        for sy in range(0, l):
                            if pro[1][sy] == pro[0]:
                                continue
                            if sy == l - 1:
                                self.addFirst(nt, self.getFirst(pro[1]))
                            elif pro[1][sy] in Upper:
                                tmp =  self.getFirst(pro[1][sy])
                                if epsilon in tmp:
                                    tmp.remove(epsilon)
                                    self.addFirst(nt, tmp)
                                else:
                                    self.addFirst(nt, tmp)
                                    break
                            else:
                                self.addFirst(nt, pro[1][sy])
                                break
        return self.First[nt]

    def addFollow(self, nt, sy):
        if isinstance(sy, str):
            sy = set([sy])
        if nt in self.Follow:
            self.Follow[nt] = self.Follow[nt].union(sy)
        else:
            self.Follow[nt] = sy

    def getFollow(self, nt):
        if nt in self.Follow:
            return self.Follow[nt]
        for pro in self.production:
            pos = pro[1].find(nt)
            if pos == -1:
                continue
            if pos + 1 == len(pro[1]):
                self.addFollow(nt, self.getFollow(pro[0]))
                self.addFollow(nt, '#')
            elif pro[1][pos + 1] not in Upper:
                self.addFollow(nt, pro[1][pos + 1])
            else:
                l = len(pro[1])
                for i in range(pos + 1, l):
                    if pro[1][i] in Upper:
                        tmp = self.getFirst(pro[1][i])
                        if epsilon in tmp:
                            tmp.remove(epsilon)
                            self.addFollow(nt, tmp)
                            if i == l - 1:
                                self.addFollow(nt, self.getFollow(pro[0]))
                        else:
                            self.addFollow(nt, tmp)
                            break
                    else:
                        self.addFollow(nt, pro[1][i])
                        break
        if nt in self.Follow:
            return self.Follow[nt]
        else:
            return set()

    def changeAction(self, stateid, sy, operation):
        if operation == '':
            self.action[stateid].pop(sy)
            return
        if isinstance(operation, str):
            operation = set([operation])
        self.action[stateid][sy] = operation

    def BuildSLR1AnalyseTable(self):
        problem_set = set()
        for stat in self.action:
            for sy in self.action[stat]:
                if len(self.action[stat][sy]) > 1:
                    problem_set.add(stat)
        self.First = dict()
        self.Follow = dict()
        movein = set()
        reduction = []
        for stat in problem_set:
            for pj in self.projectSet[stat]:
                pos = pj[1].find(dot) + 1
                if pos == len(pj[1]):
                    reduction.append((self.production_numdict[pj[0]][pj[1]], self.getFollow(pj[0])))
                else:
                    if pj[1][pos] in Upper:
                        movein = movein.union(self.getFirst(pj[1][pos]))
                    else:
                        movein.add(pj[1][pos])

            reduction.append(movein)
            l = len(reduction)
            for i in range(0, l):
                for j in range(0, l):
                    if i == j:
                        continue
                    if isinstance(reduction[i], tuple):
                        followi = reduction[i][1]
                    else:
                        followi = reduction[i]
                    if isinstance(reduction[j], tuple):
                        followj = reduction[j][1]
                    else:
                        followj = reduction[j]
                    if len(followi.intersection(followj)):
                        print("It's not a SLR(1) grammer.")
                        return False
            reduction.pop()

            for sy in self.dfa.symbol.union(set('#')):
                if sy in movein:
                    self.changeAction(stat, sy, 'S' + str(self.GO(stat, sy)))
                else:
                    flag = 1
                    for fol in reduction:
                        if sy in fol[1]:
                            self.changeAction(stat, sy, 'r' + str(fol[0]))
                            flag = 0
                            break
                    if flag:
                        self.changeAction(stat, sy, '')
            movein = set()
            reduction = []
        print("It's a SLR(1) grammer.")
        return True

    def addLATerminal(self, set_num, project, sy):
        if isinstance(sy, str):
            sy = set([sy])
        if set_num in self.LATerminal and project in self.LATerminal[set_num]:
            self.LATerminal[set_num][project] = self.LATerminal[set_num][project].union(sy)
        else:
            self.LATerminal[set_num][project] = sy

    def getClosureLATerminal(self, fromexp, setnum, searchsy):
        pst = set()
        for toexp in self.projects[fromexp]:
            if toexp.find(dot) == 0:
                pst.add((fromexp, toexp, tuple(searchsy)))
                self.addLATerminal(setnum, (fromexp, toexp), searchsy)
        return pst

    def getProjectSetLATerminal(self, pst, setnum):
        vis = set()
        while len(vis) != len(pst):
            for pj in pst:
                tpj = (pj[0], pj[1])
                if pj in vis:
                    continue
                vis.add(pj)
                nxtpos = pj[1].find(dot) + 1
                if nxtpos == len(pj[1]) or pj[1][nxtpos] not in Upper:
                    continue
                nxtposLA = nxtpos + 1
                if nxtposLA == len(pj[1]):
                    if setnum not in self.LATerminal or tpj not in self.LATerminal[setnum]:
                        vis.remove(pj)
                        continue
                    sy = self.LATerminal[setnum][tpj]
                elif pj[1][nxtposLA] not in Upper:
                    sy = pj[1][nxtposLA]
                else:
                    sy = self.getFirst(pj[1][nxtpos])
                pst = pst.union(self.getClosureLATerminal(pj[1][nxtpos], setnum, sy))
        return pst

    def BuildDFA(self): # DFA that contains lookahead terminals
        self.sy2stat = defaultdict(defaultdict)
        self.projectSet = dict()
        self.transitions = dict()

        # lookahead terminals 向前搜索符 LATerminal[project_set_num][project] = symbol_set
        self.LATerminal = defaultdict(defaultdict)
        self.projectset_num = 0
        self.dfa.setStart(0)
        q = [0]
        self.addLATerminal(0, self.sorted_projects[1], '#')
        self.projectSet[0] = {(self.sorted_projects[1][0], self.sorted_projects[1][1], ('#',))}
        while len(q):
            Iid = q.pop()
            self.projectSet[Iid] = self.getProjectSetLATerminal(self.projectSet[Iid], Iid)
            tmpdict = dict()
            tmp_LATerminal = defaultdict(defaultdict)  # 记录项目间转移时的向前搜索符
            for pj in self.projectSet[Iid]:
                nxtpos = pj[1].find(dot) + 1
                if nxtpos == len(pj[1]):
                    continue
                nxtsy = pj[1][nxtpos]
                nxtpj = pj[1][:nxtpos - 1] + nxtsy + dot + pj[1][nxtpos + 1: ]
                tpj = (pj[0], pj[1])
                if nxtsy in tmpdict:
                    tmpdict[nxtsy].add((pj[0], nxtpj, tuple(self.LATerminal[Iid][tpj])))
                else:
                    tmpdict[nxtsy] = set([(pj[0], nxtpj, tuple(self.LATerminal[Iid][tpj]))])
                if nxtsy in tmp_LATerminal and (pj[0], nxtpj) in tmp_LATerminal[nxtsy]:
                    tmp_LATerminal[nxtsy][(pj[0], nxtpj)] = tmp_LATerminal[nxtsy][(pj[0], nxtpj)].union(self.LATerminal[Iid][tpj])
                else:
                    tmp_LATerminal[nxtsy][(pj[0], nxtpj)] = self.LATerminal[Iid][tpj]

            for nxtsy in tmpdict:
                tmpdict[nxtsy] = self.getProjectSet(tmpdict[nxtsy])
                if tmpdict[nxtsy] in self.projectSet.values():
                    self.sy2stat[Iid][nxtsy] = list(self.projectSet.keys())[list(self.projectSet.values()).index(tmpdict[nxtsy])]
                    continue
                nxtIid, flag = self.getNxtStateId(Iid, nxtsy)
                if flag:
                    q.append(nxtIid)
                self.addProjectSet(nxtIid, tmpdict[nxtsy])
                for sy in tmp_LATerminal:
                    for pj in tmp_LATerminal[sy]:
                        self.addLATerminal(nxtIid, pj, tmp_LATerminal[sy][pj])
                self.dfa.addTransition(Iid, nxtIid, nxtsy)

    def BuildLR1AnalyseTable(self):
        self.action = dict()
        self.goto = dict()
        for Iid in self.projectSet:
            for pj in self.projectSet[Iid]:
                tpj = (pj[0], pj[1])
                nxtpos = pj[1].find(dot) + 1
                if nxtpos == len(pj[1]):
                    if self.projects[pj[0]][pj[1]] == 2:
                        self.addAction(Iid, '#', 'acc')
                    else:
                        op = 'r' + str(self.production_numdict[pj[0]][pj[1]])
                    if self.production_numdict[pj[0]][pj[1]] == 0:
                        continue
                    if '#' in self.LATerminal[Iid][tpj]:
                        self.addAction(Iid, '#', op)
                    for sy in self.dfa.symbol:
                        if sy in self.LATerminal[Iid][tpj]:
                            self.addAction(Iid, sy, op)
                    continue
                nxtsy = pj[1][nxtpos]
                op = 'S' + str(self.GO(Iid, nxtsy))
                if nxtsy not in Upper:
                    self.addAction(Iid, nxtsy, op)
                else:
                    self.addGoto(Iid, nxtsy, int(op[1:]))

        for stat in self.action:
            for sy in self.action[stat]:
                if len(self.action[stat][sy]) > 1:
                    print("It's not a LR(1) grammer.")
                    return False
        print("It's a LR(1) grammer.")
        return True