## Syntax-Analysis

### DFA Sample Generation

#### LR(0) DFA

- Sample LR(0) grammer
    ```bash
    E->E+T|T
    T->(E)|d
    # should not have new line at the end of the file
    ```
- Sample-generated DFA: <br>
![sample LR(0) DFA](img/sample_LR(0)_dfa.png)

#### LR(1) DFA

- Sample LR(1) grammer
    ```
    E->(L,E)|F
    L->L,E|E
    F->(F)|d
    ```
- Sample-generated DFA: <br>
![sample LR(1) DFA](img/sample_LR(1)_dfa.png)