CREATE TABLE inproceedings (
    pubkey VARCHAR(255) PRIMARY KEY,
    title VARCHAR(255),
    booktitle VARCHAR(255),
    yearx INT,
    area VARCHAR(255)
);

CREATE TABLE article (
    pubkey VARCHAR(255) PRIMARY KEY,
    title VARCHAR(255),
    journal VARCHAR(255),
    yearx INT
);

CREATE TABLE authorship (
    pubkey VARCHAR(255),
    author VARCHAR(255),
    PRIMARY KEY(pubkey, author)    
);
