'''
Boolean Formula Parse Tree node
'''
class BNode:
    """
    A class used to define the nodes of syntax tree of Boolean formula

    Attributes
    ----------
    val: string
        one of the following: logical/arithmetic/string/comparison operator, const or var
    type: string
        one of the following: log, pred, expr, var, const
    children: list of BNode
        child nodes of the current node, usually have size 1 or 2
    z3_formula: string
        z3 formula represents the entire subtree rooted at the node, can be passed to eval() directly
    size: int
        the size of subtree
    bounds: (string, string)
        lowerbound and upperbound in z3-eval-ready format, update dynamically


    Methods
    -------
    getZ3: string
        return a formula that can be passed to z3 eval() function for evaluation
    get_size: int
        return the size of the tree/subtree, note that a predicate is of size 1
    """

    def __init__(self, val, type, select_xid=None, parent=None):
        self.val = val
        self.type = type        # log, pred, expr, var, const
        self.children = []      # [0] is left child, [1] is right child
        self.z3_formula = None
        self.size = 0
        self.select_xid = select_xid
        self.bounds = None
        self.parent = parent


    def getZ3(self):
        # if z3_formula exists
        if self.z3_formula:
            return self.z3_formula

        if self.children:
            if self.type == 'log':
                if self.val == 'Not':
                    self.z3_formula = f'Not({self.children[0].getZ3()})'
                elif self.val in ['And', 'Or']:
                    self.z3_formula = f'{self.val}({self.children[0].getZ3()}, {self.children[1].getZ3()})'
                else:
                    raise NotImplementedError(f'{self.val} is not a supported logical operator.')

            elif self.type == 'pred':
                # comparison: <, >, <=, >=, =, <>, like
                if self.val == 'like':
                    # assuming left is expr or var, and right is always const
                    left, right = self.children[0], self.children[1]
                    arr = right.getZ3().split('%')
                    if len(arr) == 0:  
                        # no %, same as ==
                        self.z3_formula = f'{self.children[0].getZ3()} == {self.children[1].getZ3()}'
                    elif len(arr[0]) == 0 and len(arr[-1]) == 0:
                        # %xxx%
                        self.z3_formula = f'Contains({left.getZ3()}, {right.getZ3()})'
                    elif len(arr[0]) == 0:
                        # %xxx
                        self.z3_formula = f'SuffixOf({left.getZ3()}, {right.getZ3()})'
                    elif len(arr[-1]) == 0:
                        # xxx%
                        self.z3_formula = f'PrefixOf({left.getZ3()}, {right.getZ3()})'
                        pass
                    else:
                        raise NotImplementedError(f'like {right.getZ3()} is not supported.')
                elif self.val == '=':
                    self.z3_formula = f'{self.children[0].getZ3()} == {self.children[1].getZ3()}'
                elif self.val == '<>':
                    self.z3_formula = f'{self.children[0].getZ3()} != {self.children[1].getZ3()}'
                elif self.val in ['<', '>', '<=', '>=']:
                    self.z3_formula = f'{self.children[0].getZ3()} {self.val} {self.children[1].getZ3()}'
                else:
                    raise NotImplementedError(f'{self.val} is not a supported comparison operator.')

            elif self.type == 'expr':
                # expr: +, -, *, /, ||, AVG, SUM, COUNT, MAX, MIN
                if self.val in ['+', '-', '*', '/']:
                    self.z3_formula = f'{self.children[0].getZ3()} {self.val} {self.children[1].getZ3()}'
                elif self.val == '||':
                    self.z3_formula = f'{self.children[0].getZ3()} + {self.children[1].getZ3()}'
                elif self.val in ['AVG', 'COUNT', 'MAX', 'MIN', 'SUM']:
                    self.z3_formula = f'{self.val}({self.children[0].getZ3()})'
                else:
                    raise NotImplementedError(f'{self.val} is not a supported operator.')

        elif self.type == 'var':
            self.z3_formula = self.val

        elif self.type == 'const':
            self.z3_formula = self.val if self.val.isnumeric() else f'StringVal({self.val})'

        else:
             raise NotImplementedError(f'Type {self.type} is not supported.')

        return self.z3_formula
        

    def get_size(self):
        if self.size > 0:
            return self.size

        if self.type == 'pred':
            self.size = 1
            return self.size

        self.size = sum([c.get_size() for c in self.children])
        return self.size


    def __repr__(self):
        return self.getZ3()
    def __str__(self):
        return self.getZ3()

