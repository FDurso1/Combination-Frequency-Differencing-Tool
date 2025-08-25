# Combination Frequency Differencing (CFD) Command Line Interface (CLI) Research Prototype

## Overview

* README.txt -- this file -- contains an overview of all the files present in this download.
Please read it thoroughly before using the CFD tool if unfamiliar.

* CFD Command Line Guide.pdf is a guide to using CFD_CLI.py. Please read it thoroughly.

* The CFD Command Line Interface, CFD_CLI.py, is the primary tool in this folder. 
For details in using it, please fully read the CFD Command Line Guide pdf.

* batch_run_CFD.py is a file useful for running multiple instances of the CFD tool in parallel.
To use it, simply follow the instructions present in the file and then run it without arguments.

* CSV_splitter.py is a file useful for splitting one CSV file containing both class and nonclass
instances into two CSV files, one containing only class instances and the other only nonclass instances.
To use it, simply follow the instructions present in the file, then run it without arguments.

* mock_toy_dataset.csv is a mock dataset containing both class and nonclass instances of toys someone considered purchasing.
You can use it to test the CSV_splitter tool.

* toy_purchased.csv and toy_avoided.csv are mock class and nonclass files respectively, and can be used to test the CFD_CLI tool.

* Lastly, pyrightconfig.json is present to avoid an IDE at strict type enforcement from complaining that all of the
safe in practice functions from the matplotlib library have the alternative return type of None, which otherwise must be considered.


## Important Notes

This is a research prototype, and results may be subject to inaccuracies and potential bugs. 
The tool provides options to explore and visualize distinguishing and missing value combinations, 
but users are advised to validate the results before using them in critical settings.

## Requirements

Python:
- Python 3.7+

Imports / Libraries:
- pandas
- numpy
- matplotlib
- matplotlib_venn
- tqdm
- termcolor
- kmeans1d

## How to Run

1. Ensure you have Python 3.7+ installed on your system.
2. Download or clone this repository to your local machine.
3. Open a terminal or command prompt and navigate to the repository directory.
4. Install all necessary libraries
5. Run the script using the command: `python CFD_CLI.py [classfile.csv] [nonclassfile.csv] [distinguishability cutoff] [-optional flags]`

## Acknowledgments

This prototype was developed for research purposes and is subject to updates and improvements.
Your feedback is valuable in enhancing the tool's performance and usability.

These tools were primarily developed by Francis Durso, with assistance from Dr. M S Raunak and Mr. Rick Kuhn

