import os
import subprocess
from multiprocessing import Pool

'''
This file is used to run multiple instances of the CFD tool in parallel.
All instance outputs will be their own separate folders with CFD's naming convention of [class name]-[nonclass name]-[cutoff].
To use this, start by editing the global FINAL variables. In order, they should be:
* CFD_SCRIPT: Your filepath to the CFD_CLI.py script
* CSV_ROOT: The folder containing all the CSVs you wish to process
* DISTINGUISHABILITY_CUTOFF: Your cutoff for distinguishability

The folder indicated by CSV_ROOT should be set up as follows:
Inside it should be a series of subfolders. Inside each subfolder should be the two CSVs you wish to compare.
These should be the only CSV files inside each subfolder. Whichever is first will be considered the class file.

For example, after navigating to batch_csvs:

C:.
├───mushed-mushpois
│       mushedi.csv
│       mushpoi.csv
│
└───real-spam
        real.csv
        spam.csv

Once you have completed these steps, you can start the batch run by simply pressing "Run Code" or similar on your IDE,
or by calling `python .\\src\\batch_run_CFD.py` from where python is accessible. 

Please also review the comments starting on line 60 for information about the optional flags which are enabled in each run.

'''

# Global FINAL variables
CFD_SCRIPT = "src\\CFD_CLI.py"
CSV_ROOT = "data\\batch_csvs"
DISTINGUISHABILITY_CUTOFF = "10"


def find_csv_pairs(folder_path):
    """Returns the two CSV file paths in the folder, sorted."""
    csvs = sorted([
        os.path.join(folder_path, f)
        for f in os.listdir(folder_path)
        if f.lower().endswith(".csv")
    ])
    if len(csvs) != 2:
        raise ValueError(f"{folder_path} does not contain exactly 2 CSV files.")
    return csvs

def run_cfd_on_pair(subfolder):
    """Calls CFD_CLI.py on a pair of CSVs in the given subfolder."""
    full_path = os.path.join(CSV_ROOT, subfolder)
    try:
        csv1, csv2 = find_csv_pairs(full_path)
        print(f"Running CFD on: {csv1}, {csv2}")
        optional_flags = "-lrogfcv --drop auto -t 3" # NOTE: Modify as you'd like based on optional flags (See CLI Guide)
        result = subprocess.run(
            ["python", CFD_SCRIPT, csv1, csv2, DISTINGUISHABILITY_CUTOFF, optional_flags],
            #NOTE that if you are ever prompted for input via the presence or absence of an optional flag,
            # such as removing the -r flag with one or more files containing duplicate rows, then the prompt will
            # NOT be accessible to you and this program WILL timeout.
            capture_output=True,
            text=True,
            timeout=900 # 900 seconds (15 minutes), adjust as needed
        )
        if result.returncode != 0:
            print(f"Error in {subfolder}:\n{result.stderr}")
        else:
            print(f"Completed {subfolder}")
    except subprocess.TimeoutExpired as ex:
        print(f"Processes timed out: {ex}")
    except Exception as e:
        print(f"Failed in {subfolder}: {e}")

def main():
    subfolders = [
        name for name in os.listdir(CSV_ROOT)
        if os.path.isdir(os.path.join(CSV_ROOT, name))
    ]

    print(f"Found {len(subfolders)} subfolders in '{CSV_ROOT}'.")

    # Use parallel processing — change Pool(4) to match CPU count
    with Pool(processes=4) as pool:
        pool.map(run_cfd_on_pair, subfolders)

if __name__ == "__main__":
    main()
