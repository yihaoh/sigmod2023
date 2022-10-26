from z3 import *
import pandas as pd
from copy import deepcopy
from qm import QM



class TruthTable:
    """
    Class TruthTable built for Hinting project.
    The main truth table contain truth value for lowerbound, upperbound, target formula given lower/upper
    and target formula contains all repair sites.

    Attributes:
    z3_formulae: z3 []
        a list of z3 formula: [lower, upper, bound target, target_rs]
    rs: z3 []
        a list of repair sites in z3
    rs_str: string []
        a list of formula strings for rs
    all_preds: string []
        a list of all syntactically unique predicates from all formulae in z3_formulae
    num_preds: int
        size of all_preds
    main: DataFrame
        truth table for lower, upper, bound target and target_rs
    constraint: DataFrame
        truth table for repair sites with all_preds

    Methods:
    extract_preds(z3_formula):
        extract all predicate strings in z3_formula, add to all_preds
    evaluate_row(pred_val, z3_formula):
        Evaluate the truth value of z3_formula using truth value assigned to each predicate in pred_val
    fill_main_table:
        fill in the main table
    fill_constraint_table:
        fill in the constraint table

    get_rs_combined_fix:
        Use QM to compute the conjunctions of all fixes in predicates in all_preds
    """

    def __init__(self, z3_formulae, repair_sites):
        self.z3_formulae = z3_formulae  # [lower, upper, target_rs]
        self.rs = repair_sites  # rs in target_rs
        self.all_preds = []
        self.all_preds_z3 = []
        self.fixes = []
        self.solver = Solver()
        self.preds_conj = eval('True')
        
        self.rs_str = [str(s) + '.rs' for s in self.rs]
        
        for f in z3_formulae:
            self.extract_preds(f)

        print('********* New Iteration *********')
        print(f"# of necessary predicates: {len(self.all_preds)}")
        print(f"# of repair sites: {len(self.rs_str)}")
        

        self.main = pd.DataFrame(columns=self.rs_str + self.all_preds + ['lower', 'upper', 'bound', 'target_rs'],
                                index=range(0, 2**(len(self.all_preds) + len(self.rs_str))))

        self.constraint = pd.DataFrame(columns=self.all_preds + ['assignments'] + self.rs_str,
                                        index=range(0, 2**len(self.all_preds)))

        self.fill_main_table()
        # print(self.main)
        self.fill_constraint_table()
        # print(self.constraint)


    def get_qm_result(self, minterms, dontcares, alias):
        qm = QM(minterms, dontcares, alias)
        sols = sorted(qm.minimize(), key=len)[0]

        if sols == '':
            return 'True'
        return sols


    def fill_constraint_table(self):
        index = 0
        end = 2 ** len(self.all_preds)
        all_assignments = [format(x, f'0{len(self.rs_str)}b') for x in range(2**len(self.rs_str))]

        # first fill in each row except for the truth value of fixes
        while index < end:
            tp_row = format(index, f'0{len(self.all_preds)}b')

            # assign truth value of variables
            for i in range(len(tp_row)):
                self.constraint.at[index, self.all_preds[i]] = tp_row[i]

            row_assignments = deepcopy(all_assignments)
            # for each combinations of truth value, look for possibilities
            for i in range(2**len(self.rs_str)):
                cur_assignment = format(i, f'0{len(self.rs_str)}b')
                bound = self.main.at[index + i * 2 ** len(self.all_preds), 'bound']
                target_rs = self.main.at[index + i * 2 ** len(self.all_preds), 'target_rs']
                if bound != target_rs and bound != 'x':
                    if cur_assignment in row_assignments:
                        row_assignments.remove(cur_assignment)
            
            self.constraint.at[index, 'assignments'] = row_assignments

            index += 1
        
        # now greedily fill in the truth value for fixes
        alias = [chr(ord('A') + x) for x in range(len(self.all_preds))]
        for i, s in enumerate(self.rs_str):
            minterms, dontcares = [], []
            for j in range(end):
                prev = 'x' if i == 0 else self.constraint.at[j, self.rs_str[i-1]]
                assignments = [x for x in self.constraint.at[j, 'assignments'] if x[i-1] == prev] if prev != 'x' else self.constraint.at[j, 'assignments']
                self.constraint.at[j, self.rs_str[i]] = '0'
                has0, has1 = False, False
                for k in range(len(assignments)):
                    if assignments[k][i] == '0':
                        has0 = True
                    else:
                        has1 = True
                if has0 and has1:
                    dontcares.append(j)
                elif has1:
                    minterms.append(j)

            raw_fix = self.get_qm_result(minterms, dontcares, alias) if minterms else 'False'
            terms = [s.strip() for s in raw_fix.split('+')]
            if raw_fix == 'True':
                self.constraint[s] = '1'
                self.fixes.append(('True', 1))
            elif raw_fix == 'False':
                self.constraint[s] = '0'
                self.fixes.append(('False', 1))
            else:
                # fill selective rows with one, all other are zero
                for t in terms:
                    j = 0
                    filterData = self.constraint
                    while j < len(t):
                        k = ord(t[j]) - ord('A')
                        if j + 1 < len(t) and t[j+1] == '\'':
                            filterData = filterData[filterData[self.all_preds[k]] == '0']
                            j += 2
                        else:
                            filterData = filterData[filterData[self.all_preds[k]] == '1']
                            j += 1
                    for idx in list(filterData.index.values):
                        self.constraint.at[idx, self.rs_str[i]] = '1'
        
                # parse raw_fix to add to self.fixes
                res = ''
                sz = 0
                for term in terms:
                    j = 0
                    cur_clause = '('
                    while j < len(term):
                        k = ord(term[j]) - ord('A')
                        if j + 1 < len(term) and term[j+1] == '\'':
                            cur_clause += f'NOT({self.all_preds[k]}) AND '
                            j += 2
                            sz += 3
                        else:
                            cur_clause += f'{self.all_preds[k]} AND '
                            j += 1
                            sz += 2
                    
                    cur_clause = cur_clause[:-5] + ')'
                    res += cur_clause + ' OR '
                sz -= 1
                self.fixes.append((res[:-4], sz))
                

        
    def fill_main_table(self):
        index = 0
        end = 2**(len(self.all_preds) + len(self.rs_str))
        self.solver.reset()

        while index < end:
            self.solver.reset()
            tp_row = format(index, f'0{len(self.rs_str) + len(self.all_preds)}b')

            # assign truth value of variables
            for i in range(len(tp_row)):
                if i < len(self.rs_str):
                    self.main.at[index, self.rs_str[i]] = tp_row[i]
                else:
                    self.main.at[index, self.all_preds[i - len(self.rs_str)]] = tp_row[i]

                    if tp_row[i] == '1':
                        self.solver.add(self.all_preds_z3[i - len(self.rs_str)])
                    else:
                        self.solver.add(Not(self.all_preds_z3[i - len(self.rs_str)]))

            if self.solver.check() == sat:
                # assign truth value for formulae
                self.main.at[index, 'lower'] = self.evaluate_row(tp_row, self.z3_formulae[0], False)
                self.main.at[index, 'upper'] = self.evaluate_row(tp_row, self.z3_formulae[1], False)
                self.main.at[index, 'bound'] = self.main.at[index, 'upper'] if self.main.at[index, 'lower'] == self.main.at[index, 'upper'] else 'x'
                self.main.at[index, 'target_rs'] = self.evaluate_row(tp_row, self.z3_formulae[2], True)
            else:
                self.main.at[index, 'lower'] = 'x'
                self.main.at[index, 'upper'] = 'x'
                self.main.at[index, 'bound'] = 'x'
                self.main.at[index, 'target_rs'] = 'x'
            index += 1
            # row_num += 1



    def extract_preds(self, z3_tree):
        if z3_tree is None:
            return
        
        cur_node = str(z3_tree.decl())
        if cur_node in ['And', 'Or']:
            self.extract_preds(z3_tree.children()[0])
            self.extract_preds(z3_tree.children()[1])
        elif cur_node == 'Not':
            self.extract_preds(z3_tree.children()[0])
        else:  # pred
            # if not self.implies(self.preds_conj, z3_tree):
            #     pred = str(z3_tree)
            #     self.all_preds.append(pred)
            #     self.all_preds_z3.append(z3_tree)
            #     self.preds_conj = And(z3_tree, self.preds_conj)
            pred = str(z3_tree)
            if pred not in self.all_preds:
                self.all_preds.append(pred)
                self.all_preds_z3.append(z3_tree)

                    
    def implies(self, a, b):
        self.solver.reset()
        self.solver.add(Not(Implies(a, b)))
        res = self.solver.check()
        return res == unsat



    def evaluate_row(self, pred_val, z3_tree, is_rs):
        if z3_tree is None:
            return '1'

        cur_node = str(z3_tree.decl())

        # if cur_node is a repair site
        if str(z3_tree) + '.rs' in self.rs_str and is_rs:
            rs_idx = self.rs_str.index(f'{str(z3_tree)}.rs')
            return pred_val[rs_idx]

        # otherwise traverse down as usual
        if cur_node in ['And', 'Or']:
            left = self.evaluate_row(pred_val, z3_tree.children()[0], is_rs)
            right = self.evaluate_row(pred_val, z3_tree.children()[1], is_rs)
            if cur_node == 'And':
                return left if right == left else '0'
            else:
                return '1' if left == '1' or right == '1' else '0'
        elif cur_node == 'Not':
            res = self.evaluate_row(pred_val, z3_tree.children()[0], is_rs)
            return '0' if res == '1' else '1'
        else:  # pred
            res = self.all_preds.index(str(z3_tree))
            return pred_val[len(self.rs_str) + res]
    