# Combination Frequency Differencing (CFD) Command Line Interface (CLI) Repository Download README

# Current Version: 1.1.0
# Please make sure you periodically check for updates.

## Overview

* README.txt -- this file -- contains an overview of all the files present in this download.
Please read it thoroughly before using the CFD tool if unfamiliar.

* CFD Command Line Guide.pdf is a guide specifically for using CFD_CLI.py. Please also read it thoroughly.

* The CFD Command Line Interface, CFD_CLI.py, is the primary tool in this folder. 

* batch_run_CFD.py is a file useful for running multiple instances of the CFD tool in parallel.
To use it, simply follow the instructions present in the file and then run it without arguments.

* CSV_splitter.py is a file useful for splitting one CSV file containing both class and nonclass
instances into two CSV files, one containing only class instances and the other only nonclass instances.
To use it, simply follow the instructions present in the file, then run it without arguments.

* mock_toy_dataset.csv is a mock dataset containing both class and nonclass instances of toys someone considered purchasing.
You can use it to test with the CSV_splitter tool.

* toy_purchased.csv and toy_avoided.csv are mock class and nonclass files respectively, and can be used to test the CFD_CLI tool.

* The \tests folder contains two primary files for testing. The first, test_CLI_metamorphic_testing.py, can be called
by calling `pytest` in the command line without arguments, provided you are in the main directory and have installed pytest. (ie, `pip install pytest`)
It will perform some metamorphic tests on the CFD_CLI tool. For an in-depth explanation of metamorphic testing, see 
https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=931851. This means of testing is necessary as there is no oracle
for the correct results.

* The other primary file in the \tests folder is error_testing.py, which will perform many calls to the CFD tool with 
randomized, and often incorrect and/or incompatible arguments, to test its ability to catch and explain errors gracefully.

## Important Notes

This is a research prototype, and results may be subject to inaccuracies and potential bugs. 
The tool provides options to explore and visualize distinguishing and missing value combinations, 
but users are advised to validate the results before using them in critical settings.

## Requirements

Python:
- Python 3.7+

Libraries:
- pandas
- numpy
- matplotlib
- matplotlib_venn
- termcolor
- tqdm
- kmeans1d

The above libraries should be automatically installed if absent when the CFD CLI tool is correctly run for the first time.

## How to Run the CFD CLI tool

1. Ensure you have Python 3.7+ installed on your system.
2. Download or clone this repository to your local machine.
3. Open a terminal or command prompt and navigate to the repository directory.
4. Run the script using the command: `python CFD_CLI.py [classfile.csv] [nonclassfile.csv] [distinguishability cutoff] [-optional flags]`

## Acknowledgments

This prototype was developed by NIST for research purposes and is subject to updates and improvements.
Your feedback is valuable in enhancing the tool's performance and usability.
