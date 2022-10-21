# built-in packages
from copy import deepcopy

# extra packages
from z3 import *
from test_info import *

# project packages
from boolean_parse_tree import BNode
from utils import *
from global_var import *
from subtree_iter import *
from ttg import TruthTable
from fg import FixGenerator
import time


COUNT = Function('COUNT', IntSort(), IntSort())
MAX = Function('MAX', IntSort(), IntSort())
MIN = Function('MIN', IntSort(), IntSort())
AVG = Function('AVG', IntSort(), IntSort())
SUM = Function('SUM', IntSort(), IntSort())


class QueryTest:
    """
    Class that contains following test:
    WHERE, GROUP BY, HAVING, SELECT

    Attributes
    ----------
    schema: dict
        table name --> [[type], [attr]]
    q1_xtree: dict
        q1 xtree
    q2_xtree: dict
        q2 xtree
    z3_var:
        table alias --> [z3 var instance, one for each attr in table]
    mapping: list
        a pair of dict, table alias --> [mutual alias]
    solver: Solver
        z3 solver object
    q1_where_tree: BNode
        syntax tree of q1 WHERE clause
    q2_where_tree BNode
        syntax tree of q2 WHERE clause


    Methods
    -------
    test_where()
        test if the where clause is correct given self.mapping, find the mininum incorrect subtree
        and propose a fix if not
    test_groupby(): list of string
        test if the GROUP BY clause is correct given self.mapping and WHERE clause of Q1, point out 
        the incorrect GROUP BY expression if not
    test_having()
        test if the HAVING conditions are correct given self.mapping, find the minimum incorrect subtree
        and propose a fix if incorrect
    test_select()
        test if the SELECT clause is correct given self.mapping, find the incorrect ones and the ones
        placed at the wrong position


    build_syntax_tree(xnode): BNode
        build syntax tree given an xnode
    trace_std_alias(select_xid, table_alias, col, attr_trace): (string, string)
        return the std table alias and column name
    check_implication(q1, q2): Bool
        return True if q1 --> q2, otherwise False

    create_bounds(syn_tree, disjoint_trees): (string, string)
        return the lowerbound and upperbound after replacing all disjoint subtrees
    verify_disjoint_subtrees(target_formula, syn_tree, disjoint_trees): Boolean
        return True if syn_tree can be fixed by replacing disjoint_trees, otherwise False
    find_smallest_subtrees(n): list
        return a set of n disjoint subtrees with minimum size


    Deprecated: old algorithm
    -------------------------
    find_min_incorrect_subtree: [(BNode, string, string)]
        return a list of triple (min-tree, qleast, qmost)
    propose_fix(qleast, qmost): string
        return an z3 formula representing the fix

    """
    def __init__(self, q1_info: QueryInfo, q2_info: QueryInfo, z3_lookup, mapping, reverse_mapping, schema=db_schema):
        self.schema = schema
        self.q1_info = q1_info
        self.q2_info = q2_info
        
        self.z3_var = z3_lookup
        self.z3_var_g = {}
        self.mapping = mapping
        self.reverse_mapping = reverse_mapping
        self.solver = Solver()

        # TODO: modify the build_syntax_tree function to use attr_trace to construct syntax tree
        self.q1_where_tree = self.build_syntax_tree(self.q1_info.flatten_where_trees, self.mapping[0], self.q1_info.attr_trace, 'self.z3_var')
        self.q2_where_tree = self.build_syntax_tree(self.q2_info.flatten_where_trees, self.mapping[1], self.q2_info.attr_trace, 'self.z3_var')

        self.q1_groupby_expr = [self.build_syntax_tree(x, self.mapping[0], self.q1_info.attr_trace, 'self.z3_var') for x in self.q1_info.flatten_groupby_exprs] if q1_info.flatten_groupby_exprs else []
        self.q2_groupby_expr = [self.build_syntax_tree(x, self.mapping[1], self.q2_info.attr_trace, 'self.z3_var') for x in self.q2_info.flatten_groupby_exprs] if q2_info.flatten_groupby_exprs else []

        self.q1_having_tree = self.build_syntax_tree(self.q1_info.flatten_having, self.mapping[0], self.q1_info.attr_trace, 'self.z3_var')
        self.q2_having_tree = self.build_syntax_tree(self.q2_info.flatten_having, self.mapping[1], self.q2_info.attr_trace, 'self.z3_var')

        self.q1_select_expr = [self.build_syntax_tree(x, self.mapping[0], self.q1_info.attr_trace, 'self.z3_var') for x in self.q1_info.flatten_select] if self.q1_info.flatten_select else []
        self.q2_select_expr = [self.build_syntax_tree(x, self.mapping[1], self.q2_info.attr_trace, 'self.z3_var') for x in self.q2_info.flatten_select] if self.q2_info.flatten_select else []

        # Combine where and having tree
        self.q1_comb_tree, self.q2_comb_tree = None, None
        if self.q1_where_tree and self.q1_having_tree:
            self.q1_comb_tree = BNode('And', 'log', select_xid=self.q1_where_tree.select_xid, parent=None)
            self.q1_comb_tree.children = [self.q1_where_tree, self.q1_having_tree]
        elif self.q1_where_tree:
            self.q1_comb_tree = self.q1_where_tree
        elif self.q1_having_tree:
            self.q1_comb_tree = self.q1_having_tree

        if self.q2_where_tree and self.q2_having_tree:
            self.q2_comb_tree = BNode('And', 'log', select_xid=self.q2_where_tree.select_xid, parent=None)
            self.q2_comb_tree.children = [self.q2_where_tree, self.q2_having_tree]
        elif self.q2_where_tree:
            self.q2_comb_tree = self.q2_where_tree
        elif self.q2_having_tree:
            self.q2_comb_tree = self.q2_having_tree

        
        self.tt = None
        self.fg = None
        self.rs_fix_pair_ttg = []
        self.rs_fix_pair_fg = []

        self.ttg_converge = [[], []]
        self.fg_converge = [[], []]


    def test_where_having_min_overall_ttg(self, num_rs=2):
        # Check where equivalence
        if self.check_implication(self.q1_comb_tree.getZ3(), self.q2_comb_tree.getZ3()) and \
            self.check_implication(self.q2_comb_tree.getZ3(), self.q1_comb_tree.getZ3()):
            print('WHERE/HAVING clauses are equivalent!')
            return

        final_rs = None
        final_fixes = None
        cost = None

        start = time.time()

        iter = RepairSitesIter(self.q2_comb_tree, num_rs, self.q1_comb_tree.get_size(), self.q2_comb_tree.get_size())
        cur_rs = iter.next()

        while cur_rs:
            # print('cur_rs len: ', len(cur_rs))
            repair_site_sz = sum([s.get_size() for s in cur_rs])
            if cost is not None and repair_site_sz > cost:
                break

            if not self.verify_repair_sites(cur_rs):
                cur_rs = iter.next()
                # print('not repairable')
                continue
            

            target_rs, lower, upper = lca(self.q2_comb_tree, self.q1_comb_tree.getZ3(), self.q1_comb_tree.getZ3())
            z3_formulae = [eval(lower), eval(upper), eval(target_rs.getZ3())]
            z3_rs = []
            for i in range(len(cur_rs)):
                z3_rs.append(eval(cur_rs[i].getZ3()))

            tt = TruthTable(z3_formulae, z3_rs)
            cur_cost = (self.q1_comb_tree.get_size() + self.q2_comb_tree.get_size()) / (2*len(z3_rs)) + repair_site_sz + sum([x[1] for x in tt.fixes])
            if cost == None or cur_cost < cost:
                final_rs = cur_rs
                final_fixes = tt.fixes
                cost = cur_cost
                self.tt = tt
            cur_rs = iter.next()

            # record
            self.ttg_converge[0].append(time.time() - start)
            self.ttg_converge[1].append(cur_cost)

        for i, s in enumerate(final_rs):
            self.rs_fix_pair_ttg.append(((translate_query_namespace(str(eval(s.getZ3())), self.reverse_mapping[1], self.q2_info.std_alias_to_info), s.get_size()), 
                                        (translate_query_namespace(final_fixes[i][0], self.reverse_mapping[1], self.q2_info.std_alias_to_info), final_fixes[i][1])))
        self.print_rs_fixes(self.rs_fix_pair_ttg)


    def test_where_having_min_overall_fg(self, num_rs=2):
        # Check where equivalence
        if self.check_implication(self.q1_comb_tree.getZ3(), self.q2_comb_tree.getZ3()) and \
            self.check_implication(self.q2_comb_tree.getZ3(), self.q1_comb_tree.getZ3()):
            print('WHERE/HAVING clauses are equivalent!')
            return

        final_rs = None
        final_fixes = None
        cost = None

        start = time.time()

        iter = RepairSitesIter(self.q2_comb_tree, num_rs, self.q1_comb_tree.get_size(), self.q2_comb_tree.get_size())
        cur_rs = iter.next()

        while cur_rs:
            
            repair_site_sz = sum([s.get_size() for s in cur_rs])
            if cost is not None and repair_site_sz > cost: # or repair_site_sz > self.q2_comb_tree.get_size() / 2:
                break

            if not self.verify_repair_sites(cur_rs):
                cur_rs = iter.next()
                # print('not repairable')
                continue
            # print('cur_rs len: ', len(cur_rs))
            fg = FixGenerator(self.q1_comb_tree, self.q2_comb_tree, self.z3_var, cur_rs, mode='baseline')
            res = fg.get_fixes()
            
            cur_cost = (self.q1_comb_tree.get_size() + self.q2_comb_tree.get_size()) / (2*len(cur_rs)) + repair_site_sz + sum([x[1][1] for x in res])
            if cost == None or cur_cost < cost:
                final_rs = cur_rs
                final_fixes = res
                cost = cur_cost
                self.fg = fg
            cur_rs = iter.next()
        
            # record
            self.fg_converge[0].append(time.time() - start)
            self.fg_converge[1].append(cur_cost)

        for i, s in enumerate(final_rs):
                self.rs_fix_pair_fg.append(((translate_query_namespace(str(eval(s.getZ3())), self.reverse_mapping[1], self.q2_info.std_alias_to_info), s.get_size()), 
                                            (translate_query_namespace(str(final_fixes[i][1][0]), self.reverse_mapping[1], self.q2_info.std_alias_to_info), final_fixes[i][1][1])))

        self.print_rs_fixes(self.rs_fix_pair_fg)

        
    def test_where_having_min_rs_ttg(self, num_rs=2):
        if not self.q1_comb_tree and not self.q2_comb_tree:
            print('No need to check WHERE/HAVING since both are not needed')
            return
        elif not self.q1_comb_tree:
            print('No need to use WHERE and HAVING in your query.')
            return
        elif not self.q2_comb_tree:
            print('No WHERE/HAVING clause detected, please reconsider your query.')
            return

        # Check where equivalence
        if self.check_implication(self.q1_comb_tree.getZ3(), self.q2_comb_tree.getZ3()) and \
            self.check_implication(self.q2_comb_tree.getZ3(), self.q1_comb_tree.getZ3()):
            print('WHERE/HAVING clauses are equivalent!')
            return

        # Not equivalent, finding repair sites
        rs = self.find_smallest_rs(num_rs)

        # prepare [lower, upper, target_rs], [rs]
        target_rs, lower, upper = lca(self.q2_comb_tree, self.q1_comb_tree.getZ3(), self.q1_comb_tree.getZ3())
        z3_formulae = [eval(lower), eval(upper), eval(target_rs.getZ3())]
        z3_rs = []
        for i in range(len(rs)):
            z3_rs.append(eval(rs[i].getZ3()))
        # z3_rs = [eval(s.getZ3()) for s in rs] cannot write this shorthand, will have namespace issue

        # get ttg
        self.tt = TruthTable(z3_formulae, z3_rs)
        for i, s in enumerate(z3_rs):
            self.rs_fix_pair_ttg.append((translate_query_namespace(str(s), self.reverse_mapping[1], self.q2_info.std_alias_to_info), 
                                        (translate_query_namespace(self.tt.fixes[i][0], self.reverse_mapping[1], self.q2_info.std_alias_to_info), self.tt.fixes[i][1])))
        self.print_rs_fixes(self.rs_fix_pair_ttg)

    
    def test_where_having_min_rs_fg(self, num_rs=2):
        if not self.q1_comb_tree and not self.q2_comb_tree:
            print('No need to check WHERE/HAVING since both are not needed')
            return
        elif not self.q1_comb_tree:
            print('No need to use WHERE and HAVING in your query.')
            return
        elif not self.q2_comb_tree:
            print('No WHERE/HAVING clause detected, please reconsider your query.')
            return

        # Check where equivalence
        if self.check_implication(self.q1_comb_tree.getZ3(), self.q2_comb_tree.getZ3()) and \
            self.check_implication(self.q2_comb_tree.getZ3(), self.q1_comb_tree.getZ3()):
            print('WHERE/HAVING clauses are equivalent!')
            return

        # Not equivalent, finding repair sites
        rs = self.find_smallest_rs(num_rs)
        # print('Repair sites: ', rs)

        self.fg = FixGenerator(self.q1_comb_tree, self.q2_comb_tree, self.z3_var, rs, mode='baseline')
        res = self.fg.get_fixes()
        for i, (s, f) in enumerate(res):
            self.rs_fix_pair_fg.append((translate_query_namespace(str(eval(s.getZ3())), self.reverse_mapping[1], self.q2_info.std_alias_to_info), 
                                        (translate_query_namespace(str(f[0]), self.reverse_mapping[1], self.q2_info.std_alias_to_info), f[1])))
        self.print_rs_fixes(self.rs_fix_pair_fg)


    def print_rs_fixes(self, rs_fix_pair):
        for i, (s, f) in enumerate(rs_fix_pair):
            print(f'Repair Site #{i}: {s[0]}')
            print(f'Repair Site size #{i}: {s[1]}')
            print(f'Fix #{i}: {f[0]}')
            print(f'Fix Size #{i}: {f[1]}')


    def test_group_by(self):
        # prepare for group by check
        if not self.q1_groupby_expr and self.q2_groupby_expr:
            print('Should not have any group by expressions.')
            return [], []
        elif self.q1_groupby_expr and not self.q2_groupby_expr:
            print('Need to use group by in your query.')
            return [], []
        
        # buid z3_var_g to check group by
        for key, value in self.z3_var.items():
            self.z3_var_g[key] = []
            for v in value:
                ty = str(v.sort())
                if ty == 'Int':
                    self.z3_var_g[key].append(Int(f'{str(v)}.g'))
                elif ty == 'String':
                    self.z3_var_g[key].append(String(f'{str(v)}.g'))
                elif ty == 'Real':
                    self.z3_var_g[key].append(Real(f'{str(v)}.g'))

        # clone the boolean formulae
        q1where_g = self.build_syntax_tree(self.q1_info.flatten_where_trees, self.mapping[0], self.q1_info.attr_trace, 'self.z3_var_g')
        # q2where_g = self.build_syntax_tree(self.q2_info.flatten_where_trees, self.mapping[1], self.q2_info.attr_trace, 'self.z3_var_g')
        q1having_g = self.build_syntax_tree(self.q1_info.flatten_having, self.mapping[0], self.q1_info.attr_trace, 'self.z3_var_g')
        # q2having_g = self.build_syntax_tree(self.q2_info.flatten_having, self.mapping[1], self.q2_info.attr_trace, 'self.z3_var_g')
        if q1where_g and q1having_g:
            q1comb_g = BNode('And', 'log', select_xid=self.q1_where_tree.select_xid, parent=None)
            q1comb_g.children = [q1where_g, q1having_g]
        elif q1where_g:
            q1comb_g = q1where_g
        elif q1having_g:
            q1comb_g = q1having_g

        # if q2where_g and q2having_g:
        #     q2comb_g = BNode('And', 'log', select_xid=self.q2_where_tree.select_xid, parent=None)
        #     q2comb_g.children = [q2where_g, q2having_g]
        # elif q2where_g:
        #     q2comb_g = q2where_g
        # elif q2having_g:
        #     q2comb_g = q2having_g

        # combine two boolean formulae
        q1exp = BNode('And', 'log')
        q2exp = BNode('And', 'log')
        q1exp.children = [self.q1_comb_tree, q1comb_g]
        q2exp.children = [self.q1_comb_tree, q1comb_g]

        # clone the group by expression
        q1g = [self.build_syntax_tree(x, self.mapping[0], self.q1_info.attr_trace, 'self.z3_var_g') for x in self.q1_info.flatten_groupby_exprs]
        q2g = [self.build_syntax_tree(x, self.mapping[1], self.q2_info.attr_trace, 'self.z3_var_g') for x in self.q2_info.flatten_groupby_exprs]
    
        # construct group by predicates
        q1gexp, q2gexp = [], []
        for i in range(len(q1g)):
            n = BNode('=', 'pred')
            n.children = [self.q1_groupby_expr[i], q1g[i]]
            q1gexp.append(n)
        for i in range(len(q2g)):
            n = BNode('=', 'pred')
            n.children = [self.q2_groupby_expr[i], q2g[i]]
            q2gexp.append(n)

        # parse group by into trees
        q1gt, q2gt = None, None
        if len(q1gexp) == 1:
            q1gt = q1gexp[0]
        else:
            q1gt = BNode('And', 'log')
            q1gt.children = [q1exp[0], q1exp[1]]
            for i in range(2, len(q1exp)):
                tp = q1gt
                q1gt = BNode('And', 'log')
                q1gt.children = [tp, q1exp[i]]
        
        if len(q2gexp) == 1:
            q2gt = q2gexp[0]
        else:
            q2gt = BNode('And', 'log')
            q2gt.children = [q2exp[0], q2exp[1]]
            for i in range(2, len(q2exp)):
                tp = q2gt
                q2gt = BNode('And', 'log')
                q2gt.children = [tp, q2exp[i]]

        # conjunct with boolean formula
        q1final = BNode('And', 'log')
        q1final.children = [q1gt, q1exp]
        q1final_z3 = q1final.getZ3()
        q2final = BNode('And', 'log')
        q2final.children = [q2gt, q2exp]
        q2final_z3 = q2final.getZ3()

        # make sure they are not equivalent
        if self.check_implication(q1final_z3, q2final_z3) and self.check_implication(q2final_z3, q1final_z3):
            print('GROUP BY clauses are equivalent.')
            return [], []

        missing, incorrect = [], []
        for i in range(len(q2gexp)):
            tp = BNode('And', 'log')
            tp.children = [q2exp, q2gexp[i]]
            if not self.check_implication(q1final_z3, tp.getZ3()):
                incorrect.append(translate_query_namespace(str(eval(self.q2_groupby_expr[i].getZ3()), self.reverse_mapping[1], self.q2_info.std_alias_to_info)))

        for i in range(len(q1gexp)):
            tp = BNode('And', 'log')
            tp.children = [q1exp, q1gexp[i]]
            if not self.check_implication(q2final_z3, tp.getZ3()):
                missing.append(translate_query_namespace(str(eval(self.q1_groupby_expr[i].getZ3()), self.reverse_mapping[1], self.q2_info.std_alias_to_info)))

        return incorrect, missing
        

    def build_syntax_tree(self, xnode, alias_to_mutual, attr_trace, z3_dict, parent=None):
        if not xnode:
            return None

        select_xid = xnode['xid'] if 'xid' in xnode else None

        if xnode['type'] == 'XBasicCallNode' or xnode['type'] == 'XConnector':
            if xnode['operator_name'] in log_ops or xnode['operator_name'] in cmp_ops:
                op_type = 'log' if xnode['operator_name'].upper() in log_ops else 'pred'
                n = BNode(xnode['operator_name'].capitalize(), op_type, select_xid, parent)
                if xnode['operator_name'].upper() == 'NOT':
                    n.children.append(self.build_syntax_tree(xnode['operands'][0], alias_to_mutual, attr_trace, z3_dict, n))
                else:
                    n.children.append(self.build_syntax_tree(xnode['operands'][0], alias_to_mutual, attr_trace, z3_dict, n))
                    n.children.append(self.build_syntax_tree(xnode['operands'][1], alias_to_mutual, attr_trace, z3_dict, n))
                return n

            elif xnode['operator_name'] in ari_ops:
                op_type = 'expr'
                op_val = '+' if xnode['operator_name'] == '||' else xnode['operator_name']
                n = BNode(op_val, op_type, select_xid, parent)
                n.children.append(self.build_syntax_tree(xnode['operands'][0], alias_to_mutual, attr_trace, z3_dict, n))
                n.children.append(self.build_syntax_tree(xnode['operands'][1], alias_to_mutual, attr_trace, z3_dict, n))
                return n

            elif xnode['operator_name'] in agg_ops:
                op_type, op_val = 'expr', xnode['operator_name']
                n = BNode(op_val, op_type, select_xid, parent)
                n.children.append(self.build_syntax_tree(xnode['operands'][0], alias_to_mutual, attr_trace, z3_dict, n))
                return n

            else:
                # don't handle this operator
                raise NotImplementedError(f'Error building syntax tree: Operator < {xnode["operator_name"]} > is not currently supported.')

        elif xnode['type'] == 'XColumnRefNode':
            # Double check to make sure form valid z3 formula
            attr_split = xnode['sql_string'].split('.')
            table_alias, column_alias = self.trace_std_alias(xnode['XSelectNode_id'], attr_split[0], attr_split[1], attr_trace)
            table_alias = alias_to_mutual[table_alias]
            table = table_alias.split('_')[0]
            col_idx = self.schema[table][1].index(column_alias)
            return BNode(f'{z3_dict}["{table_alias}"][{col_idx}]', 'var', select_xid, parent)

        elif xnode['type'] == 'XLiteralNode':
            return BNode(xnode['sql_string'], 'const', select_xid, parent)

        elif xnode['type'] == 'XColumnRenameNode':
            return self.build_syntax_tree(xnode['operand'], alias_to_mutual, attr_trace, z3_dict, parent)
        
        # Node type not supported
        raise NotImplementedError(f'Building Syntax Tree Error: Do not support node type {xnode["type"]}.')


    def trace_std_alias(self, select_xid, table_alias, col, attr_trace):
        next_attr = attr_trace[(select_xid, table_alias, col)]

        while next_attr[-1] != 'std':
            next_attr = attr_trace[(next_attr[0], next_attr[1], next_attr[2])]
            if next_attr[-1] == 'expr':
                raise ValueError(f'bool_test: trace_std_alias: column ({next_attr[0], next_attr[1]}) did not expand properly.')

        return next_attr[0], next_attr[1]
    

    def check_implication(self, q1, q2):
        q1 = eval(q1) if type(q1) == str else q1
        q2 = eval(q2) if type(q2) == str else q2

        # print(f'q1: {q1}')
        # print(f'q2: {q2}')
        self.solver.reset()
        self.solver.add(Not(Implies(q1, q2)))
        res = self.solver.check()
        
        # print(f'result: {res}')
        # print('=============================')
        return res == unsat


    def create_bounds(self, syn_tree, disjoint_trees):
        if not disjoint_trees:
            return (syn_tree.getZ3(), syn_tree.getZ3())

        if syn_tree in disjoint_trees:
            syn_tree.bounds = ('False', 'True')
            return syn_tree.bounds
        elif not syn_tree.children or syn_tree.type == 'pred':
            syn_tree.bounds = (syn_tree.getZ3(), syn_tree.getZ3())
            return syn_tree.bounds

        final_bounds = None

        if len(syn_tree.children) == 1:
            child_bounds = self.create_bounds(syn_tree.children[0], disjoint_trees)
            final_bounds = (f'{syn_tree.val}({child_bounds[1]})', f'{syn_tree.val}({child_bounds[0]})')
        elif len(syn_tree.children) == 2:
            left_bounds = self.create_bounds(syn_tree.children[0], disjoint_trees)
            right_bounds = self.create_bounds(syn_tree.children[1], disjoint_trees)
            final_bounds = (f'{syn_tree.val}({left_bounds[0]}, {right_bounds[0]})', 
                            f'{syn_tree.val}({left_bounds[1]}, {right_bounds[1]})')

        syn_tree.bounds = final_bounds
        return final_bounds


    def verify_repair_sites(self, disjoint_trees):
        lower, upper = self.create_bounds(self.q2_comb_tree, disjoint_trees)
        target_formula = self.q1_comb_tree.getZ3()

        if self.check_implication(lower, target_formula) and self.check_implication(target_formula, upper):
            return True

        return False


    def find_smallest_rs(self, n):
        iter = RepairSitesIter(self.q2_comb_tree, n, self.q1_comb_tree.get_size(), self.q2_comb_tree.get_size())
        subtrees = iter.next()

        while subtrees:
            if self.verify_repair_sites(subtrees):
                return subtrees     # got results

            subtrees = iter.next()

        return []


    def test_select(self):
        select_err = []
        select_missing_idx = [True for i in range(len(self.q1_select_expr))]
        select_out_of_place_idx = [True for i in range(len(self.q2_select_expr))]

        for i in range(len(self.q2_select_expr)):
            satisfied = False
            for j in range(len(self.q1_select_expr)):
                # TODO: probably won't be able to support cmp operators in expr, need to check this
                rhs = f'{self.q1_select_expr[j].getZ3()} == {self.q2_select_expr[i].getZ3()}'
                
                # might have type mismatch, simply continue if that's the case
                try:
                    if self.check_implication(eval(self.q1_where_tree.getZ3()), eval(rhs)):
                        select_missing_idx[j] = False
                        satisfied = True
                        if i == j:
                            select_out_of_place_idx[i] = False
                        break
                except Exception as e:
                    continue
                    
            if not satisfied:
                select_out_of_place_idx[i] = False
                select_err.append(translate_query_namespace(str(eval(self.q2_select_expr[i].getZ3())),
                                                            self.reverse_mapping[1], self.q2_info.std_alias_to_info))

        select_missing, select_out_of_place = [], []
        for i in range(len(self.q1_select_expr)):
            if select_missing_idx[i]:
                select_missing.append(translate_query_namespace(str(eval(self.q1_select_expr[i].getZ3())), 
                                                                self.reverse_mapping[0], self.q1_info.std_alias_to_info))
        
        for i in range(len(self.q2_select_expr)):
            if select_out_of_place_idx[i]:
                select_out_of_place.append(translate_query_namespace(str(eval(self.q2_select_expr[i].getZ3())), 
                                                                     self.reverse_mapping[1], self.q2_info.std_alias_to_info))

        return select_err, select_out_of_place #, select_missing


    def test_eval(self, f):
        print(eval(f))
        print(str(eval(f)))
        return str(eval(f)) 