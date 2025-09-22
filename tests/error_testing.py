import os
import subprocess
from itertools import combinations
import sys
import random
import string

# Global FINAL variables
CFD_SCRIPT = "src\\CFD_CLI.py"
CSV_ROOT = "data"
DISTINGUISHABILITY_CUTOFF = "5"

def find_all_csv(folder_path):
    """Returns the two CSV file paths in the folder, sorted."""
    csvs = sorted([
        os.path.join(folder_path, f)
        for f in os.listdir(folder_path)
        if f.lower().endswith(".csv")
    ])
    return csvs

def run_cfd_on_pair():
    """Calls CFD_CLI.py on a pair of CSVs in the given subfolder."""
    full_path = os.path.join(CSV_ROOT)
    try:
        allCSVs = find_all_csv(full_path)
        for (csv1, csv2) in combinations(allCSVs, 2):

            print(f"Running CFD on: {csv1}, {csv2}")
            try:
                result = subprocess.run(
                    ["python", CFD_SCRIPT, csv1, csv2, DISTINGUISHABILITY_CUTOFF, "-lrocv", "-t", "2", "--out", "error_test_outputs"],
                    capture_output=True,
                    text=True,
                    timeout=10 # 10 seconds
                )
                if result.returncode != 0:
                    print(f"Error in {csv1}, {csv2}:\n{result.stderr}")
                    if result.returncode != 1:
                        print(f"UNCAUGHT ERROR in {csv1} / {csv2}:\n{result.stderr}")
                        sys.exit(3)
                else:
                    print(f"Completed {csv1}, {csv2}")
            except Exception as ex:
                print(f"{ex}")
    except subprocess.TimeoutExpired as ex:
        print(f"Processes timed out: {ex}")
    except Exception as e:
        print(f"Failed: {e}")

def random_error_testing():
    full_path = os.path.join(CSV_ROOT)
    
    try:
        allCSVs = find_all_csv(full_path)
        for (csv1, csv2) in combinations(allCSVs, 2):
            use_pair = random.uniform(1, 6)
            if use_pair <= 2:
                continue # skip this pair
            
            alphanumeric_chars = string.ascii_letters + string.digits
            base_args = "-orcv --out error_test_outputs"
            bad_arg = random.uniform(1, 10)
            if bad_arg <= 2:
                base_args += 'q'
            t = "2"
            bad_t = random.uniform(1, 10)
            if bad_t <= 2:
                t = random.choice(alphanumeric_chars)
                
            bad_x = random.uniform(1, 10)
            DISTINGUISHABILITY_CUTOFF = "5"
            if bad_x <= 2:
                DISTINGUISHABILITY_CUTOFF = random.choice(alphanumeric_chars)
                try:
                    if int(DISTINGUISHABILITY_CUTOFF) >= 1:
                        DISTINGUISHABILITY_CUTOFF = "-" + DISTINGUISHABILITY_CUTOFF
                except:
                    pass
            
            whoops_1 = random.uniform(1, 10)
            if whoops_1 <= 2:
                csv1 = csv2
            elif whoops_1 >= 8:
                csv2 = ""
            try:
                result = subprocess.run(
                    ["python", CFD_SCRIPT, csv1, csv2, DISTINGUISHABILITY_CUTOFF, base_args, "-t", t],
                    capture_output=True,
                    text=True,
                    timeout=10 # 10 seconds
                )
                if result.returncode != 0:
                    print(f"Error in {csv1}, {csv2}:\n{result.stderr}")
                    if result.returncode != 1:
                        print(f"UNCAUGHT ERROR in {csv1} / {csv2}:\n{result.stderr}")
                        sys.exit(3)
                else:
                    print(f"Completed {csv1}, {csv2}")
            except Exception as ex:
                print(f"{ex}")
    except subprocess.TimeoutExpired as ex:
        print(f"Processes timed out: {ex}")
    except Exception as e:
        print(f"Failed: {e}")

def main():
    full_path = os.path.join(CSV_ROOT)
    allCSVs = find_all_csv(full_path)
    print(f"Found {len(allCSVs)} CSVs in '{CSV_ROOT}'.")
    random_error_testing()

if __name__ == "__main__":
    main()
