import logging, LR

Number = [chr(i) for i in range(ord('0'), ord('9') + 1)]
epsilon = 'ε'
placeholder = '-'

def calc(a, op, b):
    if op == '+':
        return a + b
    elif op == '-':
        return a - b
    elif op == '/':
        if b == 0:
            logging.critical("divided by zero")
            exit(0)
        return a / b
    else:
        return a * b

def sign(op, b):
    if op == '-':
        return -b
    else:
        return b

def Calculate(lr_syntax, exp):
    statstack = [0]
    systack = ['#']
    calcstack = [placeholder]
    inpstack = '#' + exp[::-1]
    while True:
        curstate = statstack[-1]
        cursy = inpstack[-1]
        if cursy in Number:
            curnum = int(cursy)
            ch = inpstack[-1]
            inpstack = inpstack[:-1]
            while inpstack[-1] in Number:
                curnum *= 10
                curnum += int(inpstack[-1])
                ch = inpstack[-1]
                inpstack = inpstack[:-1]
            inpstack += ch
            cursy = 'd'
        op = list(lr_syntax.action[curstate][cursy])[0]
        if op[0] == 'S':
            systack.append(inpstack[-1])
            inpstack = inpstack[:-1]
            statstack.append(int(op[1:]))
            if cursy == 'd':
                calcstack.append(curnum)
            else:
                calcstack.append(placeholder)
        elif op[0] == 'r':
            production = lr_syntax.production[int(op[1:])]
            opnum = len(production[1])
            if opnum == 3 and '(' not in production[1]:
                num1 = calcstack[-3]
                num2 = calcstack[-1]
                ans = calc(num1, systack[-2], num2)
            elif opnum == 3:
                ans = calcstack[-2]
            elif opnum == 2:
                ans = calc2(systack[-2], calcstack[-1])
            statstack = statstack[:-opnum]
            systack = systack[:-opnum]
            statstack.append(list(lr_syntax.goto[statstack[-1]][production[0]])[0])
            systack.append(production[0])
            if opnum != 1:
                calcstack = calcstack[:-opnum]
                calcstack.append(ans)
        elif op == 'acc':
            return calcstack[-1]

def expressionCalc(lr_struct):
    while True:
        try:
            exp = input('Please input a expression: ')
            print(Calculate(lr_struct, exp))
        except EOFError:
            break

if __name__ == '__main__':
    logging.basicConfig(level = logging.WARNING)

    f = open('calc.txt', 'r', encoding='UTF-8')
    a = LR.LR()
    a.scan(f)
    a.BuildSimpleDFA()

    if a.BuildLR0AnalyseTable():
        expressionCalc(a)
    elif a.BuildSLR1AnalyseTable():
        expressionCalc(a)