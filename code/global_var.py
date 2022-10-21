# extra packages
from email.policy import default
import jpype
import jpype.imports
jpype.startJVM(classpath=['sqlanalyzer.jar'])



# pre-define a schema here
# db_schema = {
#     'drinker': [['string', 'string'], ['name', 'address']],
#     'bar': [['string', 'string'], ['name', 'address']],
#     'beer': [['string', 'string'], ['name', 'brewer']],
#     'frequents': [['string', 'string', 'int'], ['drinker', 'bar', 'times_a_week']],
#     'serves': [['string', 'string', 'float'], ['bar', 'beer', 'price']],
#     'likes': [['string', 'string'], ['drinker', 'beer']]
# }

# db_schema = {
#     'inproceedings': [['string', 'string', 'string', 'int', 'string'], ['pubkey', 'title', 'booktitle', 'yearx', 'area']],
#     'article': [['string', 'string', 'string', 'int'], ['pubkey', 'title', 'journal', 'yearx']],
#     'authorship': [['string', 'string'], ['pubkey', 'author']]
# }
db_schema = {
    'part': [['string', 'string', 'string', 'string', 'string', 'int', 'string', 'float', 'string'],
                ['p_partkey', 'p_name', 'p_mfgr', 'p_brand', 'p_type', 'p_size', 'p_container', 'p_retailprice', 'p_comment']
    ],
    'supplier': [['string', 'string', 'string', 'string', 'string', 'float', 'string'],
                    ['s_suppkey', 's_name', 's_address', 's_nationkey', 's_phone', 's_acctbal', 's_comment']
    ],
    'partsupp': [['string', 'string', 'string', 'float', 'string'],
                    ['ps_partkey', 'ps_suppkey', 'ps_availqty', 'ps_supplycost', 'ps_comment']
    ],
    'customer': [['string', 'string', 'string', 'string', 'string', 'float', 'string', 'string'],
                    ['c_custkey', 'c_name', 'c_address', 'c_nationkey', 'c_phone', 'c_acctbal', 'c_mktsegment', 'c_comment']
    ],
    'nation': [['string', 'string', 'string', 'string'], 
                ['n_nationkey', 'n_name', 'n_regionkey', 'n_comment']
    ],
    'region': [['string', 'string', 'string'],
                ['r_regionkey', 'r_name', 'r_comment']
    ],
    'lineitem': [['string', 'string', 'string', 'string', 'int', 'float', 'float', 'float', 'string', 'string', 'int', 'int', 'int', 'string', 'string', 'string'],
                    ['l_orderkey', 'l_partkey', 'l_suppkey', 'l_linenumber', 'l_quantity', 'l_extendedprice', 'l_discount', 'l_tax', 'l_returnflag', 'l_linestatus', 'l_shipdate', 'l_commitdate', 'l_receiptdate', 'l_shipinstruct', 'l_shipmode', 'l_comment']
    ],
    'orders': [['string', 'string', 'string', 'float', 'int', 'string', 'string', 'string', 'string'],
                ['o_orderkey', 'o_custkey', 'o_orderstatus', 'o_totalprice', 'o_orderdate', 'o_orderpriority', 'o_clerk', 'o_shippriority', 'o_comment']
    ]
}


# pre-define an analyzer
# default_analyzer = Analyzer('localhost', 'beers', 'postgres', 'change_me')
# default_analyzer = Analyzer('localhost', 'dblp', 'postgres', 'postgres')
default_analyzer = Analyzer('localhost', 'tpc', 'postgres', 'postgres')


# predefine supported operators
log_ops = ['AND', 'OR', 'NOT']
cmp_ops = ['>', '>=', '<', '<=', '=', '!=', '<>']
agg_ops = ['COUNT', 'MAX', 'MIN', 'AVG', 'SUM']
ari_ops = ['+', '-', '*', '/', '||']
