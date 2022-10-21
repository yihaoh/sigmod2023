from z3 import *
import pandas as pd
from copy import deepcopy
from qm import QM
from boolean_parse_tree import BNode



class FixGenerator:

    def __init__(self, q1: BNode, q2: BNode, z3_var, repair_sites, mode='baseline'):
        self.target = q1
        self.root = q2
        self.z3_var = z3_var
        self.rs = repair_sites
        self.mode = mode  # baseline, improved, aggressive
        self.result = None
        

        self.all_preds = []
        self.all_preds_z3 = []

        

        self.solver = Solver()
        # tt = pd.DataFrame(columns=self.all_preds + ['lower', 'upper', 'final'], index=range(0, 2**(len(self.all_preds))))


    def get_fixes(self):
        self.result = self.baseline(self.root, eval(self.target.getZ3()), eval(self.target.getZ3()), self.rs)
        return self.result



    # root is BNode, target is z3, rs is list of BNode
    def baseline(self, root, lower, upper, rs):
        if root in rs:
            # if not self.all_preds:
            self.all_preds = []
            self.all_preds_z3 = []
            self.extract_preds(lower)
            self.extract_preds(upper)
            target = self.minimize_target(lower, upper)
            return [(root, target)]

        # simply invert target if not
        if len(root.children) == 1:
            return self.baseline(root.children[0], Not(upper), Not(lower), rs)
        
        left_res, right_res = [], []
        new_lower, new_upper = None, None
        # if left subtree contains repair site
        if root.children[0].bounds[0] != root.children[0].bounds[1]:
            if root.val == 'And':
                new_lower = Or(lower, eval(root.children[0].bounds[0]))
                new_upper = And(Or(upper, Or(eval(root.children[0].bounds[0]), Not(eval(root.children[1].bounds[1])))), eval(root.children[0].bounds[1]))
            elif root.val == 'Or':
                new_lower = Or(And(lower, And(eval(root.children[0].bounds[1]), Not(eval(root.children[1].bounds[0])))), eval(root.children[0].bounds[0]))
                new_upper = And(upper, eval(root.children[0].bounds[1]))
            left_res = self.baseline(root.children[0], new_lower, new_upper, rs)

        # if right subtree contains repair site
        if root.children[1].bounds[0] != root.children[1].bounds[1]:
            if root.val == 'And':
                new_lower = Or(lower, eval(root.children[1].bounds[0]))
                new_upper = And(Or(upper, Or(eval(root.children[1].bounds[0]), Not(eval(root.children[0].bounds[1])))), eval(root.children[1].bounds[1]))
            elif root.val == 'Or':
                new_lower = Or(And(lower, And(eval(root.children[1].bounds[1]), Not(eval(root.children[0].bounds[0])))), eval(root.children[1].bounds[0]))
                new_upper = And(upper, eval(root.children[1].bounds[1]))
            # reset all_pred
            right_res = self.baseline(root.children[1], new_lower, new_upper, rs)

        return left_res + right_res


    def baseline_optimized(self, root: BNode, target, rs: list):
        if root in rs:
            return [(root, target)]

        # derive
        if len(root.children) == 1:
            new_target = f'Not({target})'
            return self.baseline(root.children[0], new_target, rs)
        
        left_res, right_res = [], []
        lower, upper = None, None

        # iteration only works when both sides contain repair sites
        if root.children[0].bounds[0] != root.children[0].bounds[1] and root.children[1].bounds[0] != root.children[1].bounds[1]:
            if root.val == 'And':
                # if root.children[0].val == root.children[1].val and root.val == root.children[0].val:
                if root.children[0].val != root.children[1].val and root.val == root.children[0].val:
                    # root and left have same log op
                    rl = Or(target, eval(root.children[1].bounds[0]))
                    ru = And(Or(target, Or(eval(root.children[1].bounds[0]), Not(eval(root.children[0].bounds[0])))), eval(root.children[1].bounds[1]))
                    ll = Or(target, eval(root.children[0].bounds[0]))
                    lu = And(Or(target, Or(eval(root.children[0].bounds[0]), Not(ru))), eval(root.children[0].bounds[1]))

                    self.all_preds, self.all_preds_z3 = [], []
                    self.extract_preds(ll)
                    self.extract_preds(lu)
                    left_target = self.minimize_target(ll, lu)
                    left_res = self.baseline(root.children[0], left_target, rs)

                    ru = And(Or(target, Or(eval(root.children[0].bounds[0]), Not(left_target))), eval(root.children[0].bounds[1]))
                    self.all_preds, self.all_preds_z3 = [], []
                    self.extract_preds(rl)
                    self.extract_preds(ru)
                    right_target = self.minimize_target(rl, ru)
                    right_res = self.baseline(root.children[1], right_target, rs)

                elif root.children[0].val != root.children[1].val and root.val == root.children[1].val:
                    # root and right have same log op
                    ll = Or(target, eval(root.children[0].bounds[0]))
                    lu = And(Or(target, Or(eval(root.children[0].bounds[0]), Not(eval(root.children[1].bounds[0])))), eval(root.children[0].bounds[1]))
                    rl = Or(target, eval(root.children[1].bounds[0]))
                    ru = And(Or(target, Or(eval(root.children[1].bounds[0]), Not(lu))), eval(root.children[1].bounds[1]))

                    self.all_preds, self.all_preds_z3 = [], []
                    self.extract_preds(rl)
                    self.extract_preds(ru)
                    right_target = self.minimize_target(rl, ru)
                    right_res = self.baseline(root.children[1], right_target, rs)

                    lu = And(Or(target, Or(eval(root.children[0].bounds[0]), Not(right_target))), eval(root.children[0].bounds[1]))
                    self.all_preds, self.all_preds_z3 = [], []
                    self.extract_preds(ll)
                    self.extract_preds(lu)
                    left_target = self.minimize_target(ll, lu)
                    left_res = self.baseline(root.children[0], left_target, rs)
                else: 
                    # same logical op And / both leaf node / one leaf node
                    ll = Or(target, eval(root.children[0].bounds[0]))
                    lu = And(Or(target, Or(eval(root.children[0].bounds[0]), Not(eval(root.children[1].bounds[0])))), eval(root.children[0].bounds[1]))
                    rl = Or(target, eval(root.children[1].bounds[0]))
                    ru = And(Or(target, Or(eval(root.children[1].bounds[0]), Not(eval(root.children[0].bounds[0])))), eval(root.children[1].bounds[1]))

            else: # val == 'Or'
                if root.children[0].val != root.children[1].val and root.val == root.children[0].val:
                    # root and left have same log op
                    rl = Or(And(target, And(eval(root.children[1].bounds[1]), Not(eval(root.children[0].bounds[0])))), eval(root.children[1].bounds[0]))
                    ru = And(target, eval(root.children[1].bounds[1]))
                    ll = Or(And(target, And(eval(root.children[0].bounds[1]), Not(rl))), eval(root.children[0].bounds[0]))
                    lu = And(target, eval(root.children[0].bounds[1]))
                    
                    self.all_preds, self.all_preds_z3 = [], []
                    self.extract_preds(ll)
                    self.extract_preds(lu)
                    left_target = self.minimize_target(ll, lu)
                    left_res = self.baseline(root.children[0], left_target, rs)

                    rl = Or(And(target, And(eval(root.children[1].bounds[1]), Not(left_target))), eval(root.children[1].bounds[0]))
                    self.all_preds, self.all_preds_z3 = [], []
                    self.extract_preds(rl)
                    self.extract_preds(ru)
                    right_target = self.minimize_target(rl, ru)
                    right_res = self.baseline(root.children[1], right_target, rs)

                elif root.children[0].val != root.children[1].val and root.val == root.children[1].val:
                    # root and right have same log op
                    ll = Or(And(target, And(eval(root.children[0].bounds[1]), Not(eval(root.children[1].bounds[0])))), eval(root.children[0].bounds[0]))
                    lu = And(target, eval(root.children[0].bounds[1]))
                    rl = Or(And(target, And(eval(root.children[1].bounds[1]), Not(ll))), eval(root.children[1].bounds[0]))
                    ru = And(target, eval(root.children[1].bounds[1]))

                    self.all_preds, self.all_preds_z3 = [], []
                    self.extract_preds(rl)
                    self.extract_preds(ru)
                    right_target = self.minimize_target(rl, ru)
                    right_res = self.baseline(root.children[1], right_target, rs)

                    ll = Or(And(target, And(eval(root.children[0].bounds[1]), Not(right_target))), eval(root.children[0].bounds[0]))
                    self.all_preds, self.all_preds_z3 = [], []
                    self.extract_preds(ll)
                    self.extract_preds(lu)
                    left_target = self.minimize_target(ll, lu)
                    left_res = self.baseline(root.children[0], left_target, rs)

                else:
                    ll = Or(And(target, And(eval(root.children[0].bounds[1]), Not(eval(root.children[1].bounds[0])))), eval(root.children[0].bounds[0]))
                    lu = And(target, eval(root.children[0].bounds[1]))
                    rl = Or(And(target, And(eval(root.children[1].bounds[1]), Not(eval(root.children[0].bounds[0])))), eval(root.children[1].bounds[0]))
                    ru = And(target, eval(root.children[1].bounds[1]))

        # if left subtree contains repair site
        elif root.children[0].bounds[0] != root.children[0].bounds[1]:
            if root.val == 'And':
                lower = Or(target, eval(root.children[0].bounds[0]))
                upper = And(Or(target, Or(eval(root.children[0].bounds[0]), Not(eval(root.children[1].bounds[1])))), eval(root.children[0].bounds[1]))
            elif root.val == 'Or':
                lower = Or(And(target, And(eval(root.children[0].bounds[1]), Not(eval(root.children[1].bounds[0])))), eval(root.children[0].bounds[0]))
                upper = And(target, eval(root.children[0].bounds[1]))
            # reset all_pred
            self.all_preds, self.all_preds_z3 = [], []
            self.extract_preds(lower)
            self.extract_preds(upper)
            new_target = self.minimize_target(lower, upper)
            left_res = self.baseline(root.children[0], new_target, rs)

        # if right subtree contains repair site
        elif root.children[1].bounds[0] != root.children[1].bounds[1]:
            if root.val == 'And':
                lower = Or(target, eval(root.children[1].bounds[0]))
                upper = And(Or(target, Or(eval(root.children[1].bounds[0]), Not(eval(root.children[0].bounds[1])))), eval(root.children[1].bounds[1]))
            elif root.val == 'Or':
                lower = Or(And(target, And(eval(root.children[1].bounds[1]), Not(eval(root.children[0].bounds[0])))), eval(root.children[1].bounds[0]))
                upper = And(target, eval(root.children[1].bounds[1]))
            # reset all_pred
            self.all_preds, self.all_preds_z3 = [], []
            self.extract_preds(lower)
            self.extract_preds(upper)
            new_target = self.minimize_target(lower, upper)
            right_res = self.baseline(root.children[0], new_target, rs)

        return left_res + right_res


    # lower and upper are z3 obj, output z3 obj
    def minimize_target(self, lower, upper):
        tt = pd.DataFrame(columns=self.all_preds + ['lower', 'upper', 'final'], index=range(0, 2**(len(self.all_preds))))
        # print("table dimension: ", 2**(len(self.all_preds)), len(self.all_preds))

        index = 0
        end = 2**(len(self.all_preds))
        self.solver.reset()

        minterms, dontcares = [], []
        alias = [chr(ord('A') + x) for x in range(len(self.all_preds))]

        while index < end:
            self.solver.reset()
            tp_row = format(index, f'0{len(self.all_preds)}b')

            # assign truth value of variables
            for i in range(len(tp_row)):
                tt.at[index, self.all_preds[i]] = tp_row[i]

                if tp_row[i] == '1':
                    self.solver.add(self.all_preds_z3[i])
                else:
                    self.solver.add(Not(self.all_preds_z3[i]))

            if self.solver.check() == sat:
                # assign truth value for formulae
                tt.at[index, 'lower'] = self.evaluate_row(tp_row, lower)
                tt.at[index, 'upper'] = self.evaluate_row(tp_row, upper)
                tt.at[index, 'final'] = tt.at[index, 'upper'] if tt.at[index, 'lower'] == tt.at[index, 'upper'] else 'x'
                if tt.at[index, 'final'] == '1':
                    minterms.append(index)
                elif tt.at[index, 'final'] == 'x':
                    dontcares.append(index)
            else:
                tt.at[index, 'lower'] = 'x'
                tt.at[index, 'upper'] = 'x'
                tt.at[index, 'final'] = 'x'
                dontcares.append(index)
            index += 1


        # no minterm, false
        if not minterms:
            return eval('False'), 1

        # minimize formula
        qm = QM(minterms, dontcares, alias)
        sols = sorted(qm.minimize(), key=len)[0]
        if sols == '':
            return eval('True'), 1

        # parse min
        terms = [s.strip() for s in sols.split('+')]
        res = None
        sz = 0
        for term in terms:
            j = 0
            cur_clause = None
            while j < len(term):
                k = ord(term[j]) - ord('A')
                if j + 1 < len(term) and term[j+1] == '\'':
                    sz += 3 if cur_clause is not None else 2
                    cur_clause = And(cur_clause, Not(self.all_preds_z3[k])) if cur_clause is not None else Not(self.all_preds_z3[k])
                    j += 2
                else:
                    sz += 2 if cur_clause is not None else 1
                    cur_clause = And(cur_clause, self.all_preds_z3[k]) if cur_clause is not None else self.all_preds_z3[k]
                    j += 1
            sz += 1 if res is not None else 0        
            res = Or(res, cur_clause) if res is not None else cur_clause
            
        return res, sz


    def evaluate_row(self, pred_val, z3_tree):
        if z3_tree is None:
            return '1'

        cur_node = str(z3_tree.decl())

        # traverse down as usual
        if cur_node in ['And', 'Or']:
            left = self.evaluate_row(pred_val, z3_tree.children()[0])
            right = self.evaluate_row(pred_val, z3_tree.children()[1])
            if cur_node == 'And':
                return left if right == left else '0'
            else:
                return '1' if left == '1' or right == '1' else '0'
        elif cur_node == 'Not':
            res = self.evaluate_row(pred_val, z3_tree.children()[0])
            return '0' if res == '1' else '1'
        else:  # pred
            pred = str(z3_tree)
            res = self.all_preds.index(str(z3_tree))
            if pred == 'True':
                return '1'
            elif pred == 'False':
                return '0'
            return pred_val[res]


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
            pred = str(z3_tree)
            if pred not in self.all_preds:
                self.all_preds.append(pred)
                self.all_preds_z3.append(z3_tree)


    