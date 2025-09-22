import pandas as pd

'''
This file is used to split a single CSV file containing both class and nonclass entries into separate class and nonclass
CSV files for use in the CFD Command Line tool. To use, modify the global FINAL variables below.

Once you have completed these steps, you can split the file by simply pressing "Run Code" or similar on your IDE,
or by calling `python CSV_splitter.py` from where python is accessible. 
'''

# Global FINAL variables
DATA_FILE = 'iterative_drop\\bots_vs_users\\bots_vs_users.csv'   # CSV containing both class and nonclass entries
SEPERATION_COLUMN = 'target'      # The name of the column on which the data should be split into class and nonclass files.
OUTPUT_TRUE_1 = 'bots.csv'  # The name of the CSV file you'd like the class entries to be added to
OUTPUT_FALSE_0 = 'users.csv'   # The name of the CSV file you'd like the nonclass entries to be added to

df = pd.read_csv(DATA_FILE)

df_true = df[df[SEPERATION_COLUMN] == 1]
# Append / modify as necessary, ex: df_true = df[df[SEPERATION_COLUMN] == '1' or df[SEPERATION_COLUMN] == 'True' or ...etc]
df_false = df[df[SEPERATION_COLUMN] == 0]
# Append / modify as necessary, ex: df_false = df[df[SEPERATION_COLUMN] == '0' or df[SEPERATION_COLUMN] == 'False' or ...etc]

# Drop the separation column since it will only slow down the proccess by finding unhelpful 1-way unique DVCs.
df_true = df_true.drop(SEPERATION_COLUMN, axis=1)
df_false = df_false.drop(SEPERATION_COLUMN, axis=1)

from pathlib import Path  # doctest: +SKIP
filepath_true = Path(f'bot_data\\{OUTPUT_TRUE_1}')  # doctest: +SKIP
filepath_true.parent.mkdir(parents=True, exist_ok=True)  # doctest: +SKIP
df_true.to_csv(filepath_true, index=False)  # doctest: +SKIP
filepath_false = Path(f'bot_data\\{OUTPUT_FALSE_0}')  # doctest: +SKIP
filepath_false.parent.mkdir(parents=True, exist_ok=True)  # doctest: +SKIP
df_false.to_csv(filepath_false, index=False)  # doctest: +SKIP

print(f"Successfully created {OUTPUT_TRUE_1} and {OUTPUT_FALSE_0}, split on {SEPERATION_COLUMN}!")