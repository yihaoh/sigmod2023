# Instruction for running code

## Disclaimer
**sqlanalyzer.jar** is the package which uses Calcite to parse SQL queries. We have customized it to suit our need but the package names inside will leak information about the authors' organization. Please do not open the **global_var_dblp.py** and **global_var_tpc.py** as they import packages from **sqlanalyzer.jar**.

In addition, we utilized a well-written library for Quine-McCluskey method. **petrick.py** and **qm.py** are from [this Github repo](https://github.com/Kumbong/quine_mccluskey/tree/5f431e2f6ce8518d720332fb2b3e45bb85caab87). The owner of the repo has no affiliation with the authors of the paper.

Please do not search our code on Github as it may also reveal authors' identity.


## Setup for running the code (Assuming Ubuntu OS)
1. Run the following command to install Java JDK-11:
```
sudo apt-get update && \
sudo apt-get install -y openjdk-11-jdk && \
sudo apt-get clean;   
```

2. Run the following command to install Postgres and make it run:
```
sudo apt-get install postgresql postgresql-contrib
sudo systemctl start postgresql.service
```

3. Make sure the the password for user "postgres" is also "postgres", as this is the credential used in the **global_var\*** files. 

4. Create a database named "dblp", then create another database named "tpc". Create tables using the create command under `create/create-dblp.sql` and `create/create-tpc.sql` respectively.

5. Install [Jupyter Notebook](https://jupyter.org/install) in order to run the .ipynb files for demo and experiment.

6. Install all required Python libraries in `requirements.txt` using ```pip install -r requirements.txt```. 

6. Good to go!

## Demo
The demo is run on the DBLP database. You do not need to change anything. Simply open **demo.ipynb** via Jupyter Notebook and follow instructions there.

## Experiments
In order to run the same experiments shown in the paper. Please change the following:

- In **test_info.py**, change the import of **global_var_dblp** to **global_var_tpc**.
- Same in the **bool_test.py**. 

Then you can follow the instruction in the **Experiments.ipynb** to reproduce experiment results. All testing TPC-H queries are under `tpc-h-test`. 