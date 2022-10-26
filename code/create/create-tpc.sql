CREATE TABLE part (
    p_partkey VARCHAR(255) PRIMARY KEY,
    p_name VARCHAR(255),
    p_mfgr VARCHAR(255),
    p_brand VARCHAR(255),
    p_type VARCHAR(255),
    p_size INT,
    p_container VARCHAR(255),
    p_retailprice REAL,
    p_comment VARCHAR(255)
);


CREATE TABLE partsupp (
    ps_partkey VARCHAR(255) PRIMARY KEY,
    ps_suppkey VARCHAR(255),
    ps_availqty VARCHAR(255),
    ps_supplycost REAL,
    ps_comment VARCHAR(255)
);


CREATE TABLE customer (
    c_custkey VARCHAR(255) PRIMARY KEY,
    c_name VARCHAR(255),
    c_address VARCHAR(255),
    c_nationkey VARCHAR(255),
    c_phone VARCHAR(255),
    c_acctbal REAL,
    c_mktsegment VARCHAR(255),
    c_comment VARCHAR(255));


CREATE TABLE supplier (
    s_suppkey VARCHAR(255) PRIMARY KEY,
    s_name VARCHAR(255), 
    s_address VARCHAR(255),
    s_nationkey VARCHAR(255),
    s_phone VARCHAR(255),
    s_acctbal REAL,
    s_comment VARCHAR(255)
);

CREATE TABLE nation (
    n_nationkey VARCHAR(255) PRIMARY KEY,
    n_name VARCHAR(255),
    n_regionkey VARCHAR(255),
    n_comment VARCHAR(255)
);

CREATE TABLE region (
    r_regionkey VARCHAR(255) PRIMARY KEY,
    r_name VARCHAR(255),
    r_comment VARCHAR(255)
);

CREATE TABLE lineitem (
    l_orderkey VARCHAR(255) PRIMARY KEY,
    l_partkey VARCHAR(255),
    l_suppkey VARCHAR(255),
    l_linenumber VARCHAR(255),
    l_quantity INT,
    l_extendedprice REAL,
    l_discount REAL,
    l_tax REAL,
    l_returnflag BOOLEAN,
    l_linestatus VARCHAR(255),
    l_shipdate INT,
    l_commitdate INT,
    l_receiptdate INT,
    l_shipinstruct VARCHAR(255),
    l_shipmode VARCHAR(255),
    l_comment VARCHAR(255)
);

CREATE TABLE orders (
    o_orderkey VARCHAR(255) PRIMARY KEY,
    o_custkey VARCHAR(255),
    o_orderstatus VARCHAR(255),
    o_totalprice REAL,
    o_orderdate INT,
    o_orderpriority VARCHAR(255),
    o_clerk VARCHAR(255),
    o_shippriority VARCHAR(255),
    o_comment VARCHAR(255)
);