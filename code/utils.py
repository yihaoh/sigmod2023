import re

def lca(root, lower, upper):
    if not root:
        return None, '', ''

    # single repair site?
    if root.bounds[0] == 'False' and root.bounds[1] == 'True':
        return root, lower, upper
    
    if len(root.children) == 2:
        if root.children[0].bounds[0] == root.children[0].bounds[1]:
            if root.val == 'And':
                new_lower = f'Or({lower}, {root.children[1].bounds[0]})'
                new_upper = f'And(Or({upper}, Or({root.children[1].bounds[0]}, Not({root.children[0].bounds[1]}))), {root.children[1].bounds[1]})'
            elif root.val == 'Or':
                new_lower = f'Or(And({lower}, And({root.children[1].bounds[1]}, Not({root.children[0].bounds[0]}))), {root.children[1].bounds[0]})'
                new_upper = f'And({upper}, {root.children[1].bounds[1]})'
            return lca(root.children[1], new_lower, new_upper)
        elif root.children[1].bounds[0] == root.children[1].bounds[1]:
            if root.val == 'And':
                new_lower = f'Or({lower}, {root.children[0].bounds[0]})'
                new_upper = f'And(Or({upper}, Or({root.children[0].bounds[0]}, Not({root.children[1].bounds[1]}))), {root.children[0].bounds[1]})'
            elif root.val == 'Or':
                new_lower = f'Or(And({lower}, And({root.children[0].bounds[1]}, Not({root.children[1].bounds[0]}))), {root.children[0].bounds[0]})'
                new_upper = f'And({upper}, {root.children[0].bounds[1]})'
            return lca(root.children[0], new_lower, new_upper)
        else: # reach lca, return
            return root, lower, upper
    elif len(root.children) == 1:
        new_lower = f'Not({upper})'
        new_upper = f'Not({lower})'
        return lca(root.children[0], new_lower, new_upper)

    # root has no child
    return root, lower, upper

# def lca(root, nodes):
#     if root in nodes:
#         return root, 1
    
#     if len(root.children) == 2:
#         left, left_cnt = lca(root.children[0])
#         right, right_cnt = lca(root.children[1])
#         if left_cnt and right_cnt:
#             return root, left_cnt + right_cnt
#         elif left_cnt:
#             return left, left_cnt
#         elif right_cnt:
#             return right, right_cnt
#         else:
#             return None, 0
#     elif len(root.children) == 1:
#         return lca(root.children[0])
    
#     # no children, leaf node but not in nodes
#     return None, 0


def sanitize_z3_output(s):
    # Replace the sequence "\n[\s]*" in a z3 generated formula with a single space
    return re.sub(r'\n[\s]*', ' ', s)


def translate_helper(q, mapping, std_alias_to_info):
    """
    Replace the mutual table names in a z3 formula with table names
    in its original query namespace

    Parameter
    ---------
    q: string
        an z3 formula in z3 namespace
    mapping: dict
        mutual table name --> table name in query namespace

    Return
    ------
    Boolean formula: string
        same formula with only table names switched to query namespace
    Current node type: string in [AND OR NOT Pred]
        know the type in order to avoid redundant parentheses when reconstructing formula
    """
    if q.startswith('And'):
        # find the split point
        p_cnt, idx = 0, 4
        while idx < len(q):
            if p_cnt == 0 and q[idx] == ',':
                left, right = q[4:idx].strip(), q[idx+1:-1].strip()
                break
            elif q[idx] == '(':
                p_cnt += 1
            elif q[idx] == ')':
                p_cnt -= 1
            idx += 1
        # split string into left and right
        left, left_type = translate_helper(left, mapping, std_alias_to_info)
        right, right_type = translate_helper(right, mapping, std_alias_to_info)
        left = f'({left})' if left_type not in ['AND', 'Pred', 'NOT'] else left
        right = f'({right})' if right_type not in ['And', 'Pred', 'NOT'] else right
        return f'{left} AND {right}', 'AND'

    elif q.startswith('Or'):
        # find the split point
        p_cnt, idx = 0, 3
        while idx < len(q):
            if p_cnt == 0 and q[idx] == ',':
                left, right = q[3:idx].strip(), q[idx+1:-1].strip()
                break
            elif q[idx] == '(':
                p_cnt += 1
            elif q[idx] == ')':
                p_cnt -= 1
            idx += 1
        # split string into left and right
        left, left_type = translate_helper(left, mapping, std_alias_to_info)
        right, right_type = translate_helper(right, mapping, std_alias_to_info)
        left = f'({left})' if left_type not in ['OR', 'Pred', 'NOT'] else left
        right = f'({right})' if right_type not in ['OR', 'Pred', 'NOT'] else right
        return f'{left} OR {right}', 'OR'

    elif q.startswith('Not'):
        return f'NOT({translate_helper(q[4:-1], mapping, std_alias_to_info)[0]})', 'NOT'

    else: # predicate
        tokens = q.strip().split()
        for i in range(len(tokens)):
            prefix = ''
            t = ''
            
            # start with some agg function
            if tokens[i].startswith('COUNT') or tokens[i].startswith('MIN') \
                or tokens[i].startswith('MAX') or tokens[i].startswith('AVG') \
                or tokens[i].startswith('Concat') or tokens[i].startswith('('):
                p_idx = tokens[i].find('(')
                prefix = tokens[i][:p_idx+1]
                t = tokens[i][p_idx+1:].split('.')
                
            # no agg function, simple predicates
            else:
                t = tokens[i].split('.')

            # check if in form of table.attr
            if len(t) == 2:
                # special case: * and / operator is not separated by space
                check1, check2 = t[0].split('*'), t[0].split('/')
                if len(check1) == 2:
                    prefix = check1[0] + ' * '
                    t[0] = check1[1]
                elif len(check2) == 2:
                    prefix = check2[0] + ' / '
                    t[0] = check2[1]

                tokens[i] = f'{prefix}{std_alias_to_info[mapping[t[0]]][-1]}.{t[1]}'
            
        return ' '.join(tokens), 'Pred'


def translate_query_namespace(q, mapping, std_alias_to_info):
    return translate_helper(q, mapping, std_alias_to_info)[0]


def get_leaf_nodes(syn_tree):
    # get all leaf nodes in left-to-right order
    if not syn_tree.children:
        return [syn_tree]

    if len(syn_tree.children) == 1:
        return get_leaf_nodes(syn_tree.children[0])

    left = get_leaf_nodes(syn_tree.children[0])
    right = get_leaf_nodes(syn_tree.children[1])

    return left + right