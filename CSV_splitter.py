import pandas as pd

'''
This file is used to split a single CSV file containing both class and nonclass entries into separate class and nonclass
CSV files for use in the CFD Command Line tool. To use, modify the global FINAL variables below.

Be sure to also review the rest of the code to best seperate your files as intended, specifically all #NOTE's.

Once you have completed these steps, you can split the file by simply pressing "Run Code" or similar on your IDE,
or by calling `python CSV_splitter.py` from where python is accessible.
'''

# Global FINAL variables
DATA_FILE = 'data\\unsplit\\mock_toy_dataset.csv'   # CSV containing both class and nonclass entries
SEPERATION_COLUMN = 'Purchased'      # The name of the column on which the data should be split into class and nonclass files.
OUTPUT_TRUE_1 = 'toy_purchased.csv'  # The name of the CSV file you'd like the class entries to be added to
OUTPUT_FALSE_0 = 'toy_avoided.csv'   # The name of the CSV file you'd like the nonclass entries to be added to
POSITIVE_RESULTS = ['Yes', 'True', 1, '1'] #, ...etc All values which should be considered positive
NEGATIVE_RESULTS = ['No', 'False', 0, '0'] #, ...etc All values which should be considered negative

df = pd.read_csv(DATA_FILE)

df_true = df[df[SEPERATION_COLUMN].isin(POSITIVE_RESULTS)]
df_false = df[df[SEPERATION_COLUMN].isin(NEGATIVE_RESULTS)]

# NOTE Alternatively, specify that the nonclass file should be all values that are not considered a positive result
# df_false = df[~df[SEPERATION_COLUMN].isin(POSITIVE_RESULTS)]


# NOTE If splitting based on whether a value is above/below a given cutoff, use this instead of either of the above
'''
pos_cutoff = 1 # inclusive (50 and above)
neg_cutoff = 1 # exclusive (strictly below 50)
df_true = df[df[SEPERATION_COLUMN].astype(float) >= pos_cutoff]
df_false = df[df[SEPERATION_COLUMN].astype(float) < neg_cutoff]
'''

# Drop the separation column since it will only slow down the proccess by finding unhelpful 1-way unique DVCs.
df_true = df_true.drop(SEPERATION_COLUMN, axis=1)
df_false = df_false.drop(SEPERATION_COLUMN, axis=1)

from pathlib import Path  
filepath_true = Path(f'data\\{OUTPUT_TRUE_1}')
filepath_true.parent.mkdir(parents=True, exist_ok=True)
df_true.to_csv(filepath_true, index=False)
filepath_false = Path(f'data\\{OUTPUT_FALSE_0}')
filepath_false.parent.mkdir(parents=True, exist_ok=True)
df_false.to_csv(filepath_false, index=False)

print(f"Successfully created {OUTPUT_TRUE_1} and {OUTPUT_FALSE_0}, split on {SEPERATION_COLUMN}!")