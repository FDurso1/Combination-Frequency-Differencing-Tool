'''
Combinatorial Frequency Differencing (CFD) is a technique used to identify patterns that distinguish one group of 
data from another by analyzing how combinations of variable values (ex, color + shape + size) appear across the groups.
Rather than looking at variables individually, CFD examines all t-way interactions (ex, 2-way, 3-way, etc.) to find 
which combinations occur distinguishingly more frequently in one file than in the other, making them Distinguishing 
Value Combinations (DVCs).

Release Version 1.1.0
Last Updated: 9/22/2025
'''

import argparse
from collections import Counter, defaultdict
from copy import deepcopy
import csv
from datetime import datetime
import importlib
from itertools import combinations, product
import os
import re
import shutil
import subprocess
import sys
import time
from typing import cast, TypeAlias

def install_and_import(pkg_name: str) -> None:

    """
    Attempts to import a package, and if it fails, installs it using pip and retries the import.
    """

    try:
        module = importlib.import_module(pkg_name)
        globals()[pkg_name] = module
    except ImportError:
        try:
            subprocess.check_call([sys.executable, "-m", "pip", "install", pkg_name])
        except:
            try:
                subprocess.check_call([sys.executable, "-m", "conda", "install", pkg_name])
            except:
                print(f"Was unable to install '{pkg_name}' automatically.\n" \
                      "Please attempt to manually install this package and then rerun.", file=sys.stderr)
                sys.exit(1)
        print(f"Installed {pkg_name}!")
        install_and_import(pkg_name) # Retry after install

if __name__ == "__main__":
    required_packages: list[str] = [
        'pandas', # Dataframes for reading CSV data
        'numpy', # Mathematical operations (mostly graph related)
        'matplotlib.pyplot', # Graph creation
        'matplotlib.axes', # Type enforcing the axes object
        'matplotlib_venn', # Venn diagram graphs specifically
        'matplotlib.colors', # Pie chart color optimization
        'termcolor', # Colored terminal output
        'tqdm', # Progress bars in terminal when logging output and operation takes > 3 seconds
        'kmeans1d' # When binning data, have the ability to bin it by kmeans clustering
    ]
    for pkg in required_packages:
        install_and_import(pkg)

import kmeans1d
import matplotlib.axes as mpl_axes
from matplotlib.backend_bases import MouseEvent as Event
from matplotlib.colors import is_color_like
import matplotlib.pyplot as plt
from matplotlib_venn import venn2
from matplotlib_venn._common import VennDiagram as Venn
import numpy as np
import pandas as pd
import termcolor
from tqdm import tqdm as tq

# Type aliases for more somewhat readable code, used in most places
ComboFrequency: TypeAlias = int
ValueIndex: TypeAlias = int
ValueString: TypeAlias = str
ValueCombo_Tuple_index_str: TypeAlias = tuple[ValueIndex, ValueString]

class CFDContext:

    """
    Context class to hold all necessary data and configuration for the CFD tool.
    This class encapsulates all the parameters and results needed for processing
    class and nonclass files, including their paths, names, data, and various flags
    for controlling the behavior of the tool.
    """

    def __init__(self):
        self.data: dict[str, int | list[list[int]] | list[dict[str, int]]] | dict[str, list[list[int]]] = {}
        '''Contains many calculated results for easy access.'''
        self.distinguishability_cutoff: float = 0.0 
        '''User chosen distinguishability cutoff.'''
        # Optional Flags:
        self.max_t_ways: int = 0
        '''User chosen flag for how many t-ways should be calculated, default is 3.'''
        self.verbose: bool = False 
        '''User chosen flag to make the outputs use variable names if present.'''
        self.logs: bool = False
        '''User chosen flag to log program execution.'''
        self.gen_graphs: bool = False
        '''User chosen flag to generate graphical outputs.'''
        self.gen_mvcs: bool = False
        '''User chosen flag to generate missing value combinations.'''
        self.overwrite: bool = False
        '''User chosen flag to auto overwrite existing files.'''
        self.remove_dups: bool = False
        '''User chosen flag to auto remove duplicate rows from data.'''
        self.complete_rows_only: bool = False
        '''User chosen flag to remove all incomplete data before processing.'''
        self.silenced: bool = False
        '''User chosen flag to silence all non-prompting, non-error terminal outputs.'''
        self.silenced_info: bool = False
        '''User chosen flag to silence all non-prompting info terminal outputs.'''
        self.silenced_ts: bool = False 
        '''User chosen flag to silence all timestamp terminal outputs.'''
        self.col_drop: str = "NONE"
        '''User specified flag to be prompted whether to drop recommended columns, or to do so automatically.'''
        self.filter: bool = False
        '''User specified flag to filter out lower t-level DVCs from higher ones.'''
        self.delimiter: str = ""
        '''User specified delimiter for the CSV files, default is a comma.'''
        self.drop_common: str = ""
        '''User specified flag to drop all common entries from either the class, nonclass, or both files.'''
        self.force: bool = False 
        '''User specified flag to ignore some error checking. Meant to be developer use only.'''
        self.output_path: str = ""
        '''User specified flag to specify an output folder path.'''
        self.all_bin_params: list[str] = []
        '''User specified binning specifications.'''
        self.do_not_bin: bool = False
        '''Do not bin any data.'''
        self.auto_bin: bool = False
        '''Automatically bin with the best binning estimate using all other specified parameters.'''
        self.bin_by_estimate: bool = False
        '''Bin via an estimation for bin size and positions.\nCurrently this uses 1D k-means clustering.'''
        self.bin_by_width: bool = False
        '''Bin by equal width bins instead of estimating bin positions.'''
        self.bin_by_freq: bool = False 
        '''Bin by equal frequency bins instead of estimating bin positions.'''
        self.set_bin_num: int = -1 
        '''Bin using a set number of bins each time.'''
        self.bin_all_vars: bool = False
        '''Bin all variables using the specified parameters, not just estimated continuous ones.'''
        # Saved Data / Calculations
        self.start_time: datetime = datetime.now()
        '''Start time of the operation.'''
        self.class_file_duplicates: list[list[str]] = []
        '''List of duplicate rows in the class file.'''
        self.nonclass_file_duplicates: list[list[str]] = []
        '''List of duplicate rows in the nonclass file.'''
        self.variable_names: list[str] = []
        '''List of variable names if present, otherwise Var 1, Var 2, etc.'''
        self.max_name_length: int = 0
        '''Length of the longest variable name (for spacing).'''
        self.ncc: int = 0
        '''Number of columns / variables / features.'''
        self.nrc: int = 0
        '''Number of rows in the class file.'''
        self.nrn: int = 0
        '''Number of rows in the nonclass file.'''
        self.class_file_data: list[list[ValueString]] = []
        '''The data from the class file.'''
        self.nonclass_file_data: list[list[ValueString]] = []
        '''The data from the nonclass file.'''
        self.has_header: bool = False
        '''Is a header present in either file.'''
        self.class_file_path: str = ""
        '''Path to the class file.'''
        self.nonclass_file_path: str = ""
        '''Path to the nonclass file.'''
        self.class_file_name: str = ""
        '''Name to the class file.'''
        self.nonclass_file_name: str = ""
        '''Name to the nonclass file.'''
        self.common_entries: list[tuple[tuple[ValueString, ...], dict[str, int]]] = []
        '''Entries present in both classes.\n\nThe tuple of strings comprises the entry, while the dictionary maps:\n
    'class_count': number of times this entry appears in the class file,
    'nonclass_count': number of times this entry appears in the nonclass file'''
        self.avg_val_per_var: float = 0.0
        '''The average number of values each variable holds.'''
        self.csv_dvc_print_tway: dict[int, list[str]] = {}
        '''Holds the dvc csv output for t-way feature value combinations.\n\nDictionary maps a t-way to its list of strings.\n
Each string in the list follows the pattern: U/D;0/1;(feature, value);frequency;frequency difference;'''
        self.combination_counts_class: dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency]] = {}
        '''Dictionary to hold combination counts for class file.\n\nDictionary maps:\n
    '[t]-way': to a second dictionary, which maps:
        A tuple containing t (index, value) tuples creating a t-way VC: its frequency within the class file.'''
        self.combination_counts_nonclass: dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency]] = {}
        '''Dictionary to hold combination counts for nonclass file.\n\nDictionary maps:\n
    '[t]-way': to a second dictionary, which maps:
        A tuple containing t (index, value) tuples creating a t-way VC: its frequency within the nonclass file.'''
        # Distinguishing tway combos dictionary
        self.distin_tway_combos: dict[str, tuple[list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]],
            list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]]]] = {}
        '''Distinguishing tway combos dictionary.\n\nIt maps:\n
    '[t]-way': a tuple of 2 identical lists of DVCs. The first is for class DVCs, the second for the nonclass DVCs. \
Each list contains tuples comprised of:
    - A tuple: t (index, value) tuples comprising a t-way DVC
    - A float: The frequency that this DVC appears in the file indicated by the position of this list (class / nonclass)
    - A float: The frequency that this DVC appears in the other file
    - An int: The number of times this DVC appears in the file indicated by the position of this list
    - An int: The number of times this DVC appears in the other file'''
        self.missing_tway_combos: dict[str, tuple[list[tuple[tuple[str, ...], list[int]]], 
            list[tuple[tuple[str, ...], list[int]]], list[tuple[tuple[str, ...], list[int]]]]] = {}
        '''Missing t-way value combinations (MVCs):\n\nIt maps:\n
    '[t]-way': a tuple of three identically shaped lists. The first for MVCs missing solely from the class file, the \
second for MVCs missing solely from the nonclass file, and the third for MVCs missing from both.
    Within the list are tuples containing:
    - A tuple of t strings, comprising the values of the MVC
    - A list of t ints, comprising the positions of those values
        '''
        self.missing_internally_all_tways: dict[str, dict[tuple[tuple[int, str], ...], tuple[bool, bool]]] = {}
        '''Holds whether a given missing value combination can be constructed using values solely from either file.\n\nIt maps:\n
    '[t]-way': a dictionary of MVCs at that t-way. This internal dictionary maps:
    A tuple of tuples of (index, value)s, comprising a given MVC: a tuple of two bools, the first for whether that MVC can be \
made using solely values present in the class file, the second for whether it can be made with with only values from the nonclass file.
        '''
        self.missing_internal_counts: dict[str, list[int]] = {}
        '''Count how many MVCs can be made with values solely from either file for all types of MVCs.\n\nIt maps:\n
    '[t]-way': a list of 12 ints, the first 4 for the class MVCs, the next 4 for the nonclass MVCs, the final 4 for the \
MVCs absent from both.
    Within each group of 4:
    - How many MVCs can be made with values from just the class file AND values from just the nonclass file
    - How many MVCs can be made with values just from the class file but NOT from the nonclass file
    - How many MVCs can be made with values just from the nonclass file but NOT from the class file
    - How many MVCs cannot be made with values from just either file
        '''
        self.num_warnings: int = 0
        '''Number of warnings the program produces (to display if logs are enabled).'''
        self.column_names_dropped: list[str] = []
        '''Names of all columns dropped if --drop flag was enabled.'''
        self.class_row_DVC_occurrence_counts: dict[int, list[int]] = {}
        '''Used for the class row DVC counts CSV.\n\nIt maps:\n
    position of the row in the file: a list of how many 1-way, 2-way, etc DVCs it contains'''
        self.nonclass_row_DVC_occurrence_counts: dict[int, list[int]] = {}
        '''Used for the nonclass row DVC counts CSV.\n\nIt maps:\n
    position of the row in the file: a list of how many 1-way, 2-way, etc DVCs it contains'''
        # Maps feature names to their original number of unique values and new bin ranges
        self.feature_bin_ranges: list[tuple[str, int, list[tuple[float, float]]]] = []
        '''When binning data, is a list of all binned features.\n
        The list contains tuples of the feature's name, the number of unique values it holds, and a list of tuples of floats \
representing the edges of each bin for that feature. Bins extend to infinity.'''
        self.grouping_options: list[list[list[float]]] = []
        '''Contain possible grouping options from bin calculations, allowing for them to be dynamically displayed.\n
        The outermost list contains all the binning configurations, from 1 bin to the maximum number of bins calculated.\n
        Each configuration is a list of list of floats. The outer list holds all the bins, while the inner lists contain \
all the original data points which fall into that bin.'''
        self.centroids: list[tuple[list[float], float]] = [([], 0)]
        '''When binning by width, centroids contains a list of each binning configuration from 1 bin to the max bins calculated.\n
        Each configuration is a tuple containing a list of floats, the centerpoints of each bin, and a float representing half the \
width of each bin.'''

def print_warning_message(context: CFDContext, message: str, is_error: bool=False, do_not_write=False) -> None:

    """
    Prints a warning message to the console and logs it to the logs file if logs are enabled.
    If the message is an error, instead print to stderr, write it to logs if logs are enabled, then exit.
    """

    output = context.output_path

    warn_type = "WARNING"
    if is_error:
        warn_type = "ERROR"

        def to_upper_except_quotes(msg: str) -> str:

            """
            Convert message to uppercase except for the parts inside quotes (to preserve case-specific flag instructions) 
            """

            result: list[str] = []
            in_single = False
            in_double = False
            for char in msg:
                if char == "'" and not in_double:
                    in_single = not in_single
                    result.append(char)
                elif char == '"' and not in_single:
                    in_double = not in_double
                    result.append(char)
                elif in_single or in_double:
                    result.append(char)
                else:
                    result.append(char.upper())
            return ''.join(result)

        message = to_upper_except_quotes(message)
        termcolor.cprint(f"ERROR: {message}.", "red", attrs=['bold'], file=sys.stderr)
    else:
        context.num_warnings += 1
        if not context.silenced:
            termcolor.cprint(f"WARNING: {message}.", "yellow", attrs=['bold'])

    if context.logs and not do_not_write: # do_not_write is just for the error resulting from too long file names
        now = datetime.now() # we would not want to try to make the resulting output folder under this circumstance
        formatted_time = now.strftime("%H:%M:%S")
        class_file_name = context.class_file_name
        nonclass_file_name = context.nonclass_file_name
        distinguishability_cutoff = context.distinguishability_cutoff
        sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
        os.makedirs(sub_dir_name, exist_ok=True)
        new_file_name = f"logs.txt"
        file_path = os.path.join(sub_dir_name, new_file_name)
        with open(file_path, "a") as file:
            file.write(f"{warn_type}: {message} - {formatted_time}\n")
            file.close()
    if is_error:
        sys.exit(1)

def print_info_message(context: CFDContext, message: str, print_anyway: bool=False) -> None:

    """
    Prints an informational message to the console and write it to the logs file if logs are enabled.
    """

    output = context.output_path

    if not (context.silenced or context.silenced_info) or print_anyway: 
        # print_anyway is used for printing info messages preceeding necessary user input
        termcolor.cprint(f"Info: {message}.", "cyan")

    if context.logs:
        now = datetime.now()
        formatted_time = now.strftime("%H:%M:%S")
        class_file_name = context.class_file_name
        nonclass_file_name = context.nonclass_file_name
        distinguishability_cutoff = context.distinguishability_cutoff
        sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
        os.makedirs(sub_dir_name, exist_ok=True)
        new_file_name = f"logs.txt"
        file_path = os.path.join(sub_dir_name, new_file_name)
        with open(file_path, "a") as file:
            file.write(f"Info: {message} - {formatted_time}\n")
            file.close()

def generate_venn_diagram_graph(context: CFDContext) -> None:

    """
    Generates a Venn diagram for the t-way interactions between class and nonclass files.
    This function creates a grid of Venn diagrams for each t-way interaction level,
    displaying the number of value interactions and distinguishing value combinations.
    The diagrams are saved as a PNG file in the specified graphs directory.
    """

    grid = cast(list[list[int]], context.data['grid'])
    distinguishing_grid = cast(list[list[int]], context.data['occur_distinguishing_list'])
    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff
    max_ways = context.max_t_ways
    output = context.output_path

    sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    graphs_dir = os.path.join(sub_dir_name, "Graphs")
    os.makedirs(graphs_dir, exist_ok=True)

    fig, axs = plt.subplots(
        nrows=max_ways, ncols=4,
        figsize=(12, 2.5 * max_ways),
        gridspec_kw={'width_ratios': [0.4, 1, 0.5, 1]}
    )

    # Adjust spacing and add column titles with precise horizontal positioning
    fig.subplots_adjust(hspace=0.6, top=0.92)
    fig.text(0.08, 0.98, "T-Way", ha='center', fontsize=14, fontweight='bold')
    fig.text(0.31, 0.98, "All Value Combinations", ha='center', fontsize=14, fontweight='bold')
    fig.text(0.84, 0.98, "Distinguishing Value Combinations", ha='center', fontsize=14, fontweight='bold')

    # Ensure axs is always 2D even if max_ways = 1
    if max_ways == 1:
        axs = [axs]

    for i in range(max_ways):
        class_VIs = grid[i][3] - grid[i][5]
        nonclass_VIs = grid[i][4] - grid[i][5]
        intersect_VIs = grid[i][5]

        distinguishing_class_VIs = distinguishing_grid[i][0]
        distinguishing_nonclass_VIs = distinguishing_grid[i][1]
        distinguishing_intersect_VIs = distinguishing_grid[i][2]

        row = [cast(mpl_axes.Axes, ax) for ax in axs[i]]

        # Turn off unused panels
        for j in range(3):
            row[j].set_axis_off()

        # Label the t-way
        row[0].text(0.5, 0.5, str(i + 1), ha='center', va='center', fontsize=14, fontweight='bold')

        # Determine whether to draw venns or display "No Applicable Data"
        if any([class_VIs, nonclass_VIs, intersect_VIs]):
            vd = venn2(subsets=(class_VIs, nonclass_VIs, intersect_VIs), set_colors=('#305CDE', 'red'), 
                set_labels=('', ''), ax=row[1])
        else:
            row[1].text(0.5, 0.5, "No Applicable Data", ha='center', va='center', fontsize=12)
            vd = None
        if any([distinguishing_class_VIs, distinguishing_nonclass_VIs, distinguishing_intersect_VIs]):
            nvd = venn2(subsets=(distinguishing_class_VIs, distinguishing_nonclass_VIs, distinguishing_intersect_VIs),
                set_colors=('#305CDE', 'red'), set_labels=('', ''), ax=row[3])
        else:
            row[3].text(0.5, 0.5, "No Applicable Data", ha='center', va='center', fontsize=12)
            nvd = None

        # Add "Class" and "Nonclass" labels if applicable
        def label_by_id(label: str, ID: str, diagram: Venn|None):
            if diagram is not None:
                diagram = cast(Venn, diagram)
                label_obj = diagram.get_label_by_id(ID)
                if label_obj:
                    num = label_obj.get_text()
                    label_obj.set_text(label + "\n" + num)
                    if ID == "10":
                        label_obj.set_x(-1.01)
                    elif ID == "01":
                        label_obj.set_x(1.01)

        for label, ID in zip(['Class', 'Nonclass'], ['10', '01']):
            label_by_id(label, ID, vd)
            label_by_id(label, ID, nvd)

    plt.tight_layout()
    filename = os.path.join(graphs_dir, "venn_diagrams.png")
    plt.savefig(filename, dpi=300, bbox_inches='tight')
    plt.close(fig)

def generate_pie_charts(context: CFDContext) -> None:

    """
    Generates pie charts for each variable in the class and nonclass files.
    Each pie chart shows the distribution of values for that variable in both files.
    The charts are saved in the Graphs subdirectory.
    """

    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff
    variable_names = context.variable_names
    data = context.data
    logs = context.logs
    silent = context.silenced or context.silenced_ts
    output = context.output_path
    nrc = context.nrc
    nrn = context.nrn

    sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    graphs_dir = os.path.join(sub_dir_name, "Graphs", "Pie Graphs")
    os.makedirs(graphs_dir, exist_ok=True)

    pie_comp_list = [i for i in range(len(variable_names))]
    val_freq_class = cast(list[dict[str, ComboFrequency]], data['val_freq_class'])
    val_freq_nonclass = cast(list[dict[str, ComboFrequency]], data['val_freq_nonclass'])

    csv_file_name = f"pie_{class_file_name}_{nonclass_file_name}_{distinguishability_cutoff}.csv"
    csv_file_path = os.path.join(graphs_dir, csv_file_name)

    for idx in tq(pie_comp_list, desc='Pie Progress', disable=(not logs or silent)):
        var_name = variable_names[idx]

        if not any(val_freq_class[idx].values()) or not any(val_freq_nonclass[idx].values()):
            print_warning_message(context, f"No pie chart data available for {var_name}")
            continue

        unique_labels_class: list[str] = list(val_freq_class[idx].keys())
        unique_labels_nonclass: list[str] = list(val_freq_nonclass[idx].keys())
        values_class: list[float] = list(val_freq_class[idx].values())
        values_nonclass: list[float] = list(val_freq_nonclass[idx].values())
        a, b = zip(*sorted(zip(unique_labels_class, values_class)))
        sorted_class_labels: list[str] = list(a)
        sorted_class_values: list[float] = list(b)
        c, d = zip(*sorted(zip(unique_labels_nonclass, values_nonclass)))
        sorted_nonclass_labels: list[str] = list(c)
        sorted_nonclass_values: list[float] = list(d)

        all_unique_labels = list(set(unique_labels_class + unique_labels_nonclass))
        colors_map = plt.colormaps['tab20']
        colors = colors_map(np.linspace(0, 1, len(all_unique_labels)))
        color_map = {label: colors[i] for i, label in enumerate(all_unique_labels)}
        # Ensure each pie slice is the same color for the same value between pie charts
        # print(f"DEBUG: {var_name}")
        # print(sorted_class_labels)
        # print(sorted_class_values)
        # input()
        # print(sorted_nonclass_labels)
        # print(sorted_nonclass_values)
        # input()
        with open(csv_file_path, 'a') as file:
            file.write(f"{var_name};Class;{';'.join(f'({a}, {round(b,4)}, {round(b/nrc, 4)})' for (a, b) in zip(sorted_class_labels, sorted_class_values))}\n")
            file.write(f"{var_name};Nonclass;{';'.join(f'({a}, {round(b,4)}, {round(b/nrn, 4)})' for (a, b) in zip(sorted_nonclass_labels, sorted_nonclass_values))}\n")
            file.close()
            
        if all(is_color_like(lbl) for lbl in all_unique_labels): # If, by chance, all the labels *are* colors, use them.
            color_map = {label: label for label in all_unique_labels}
        try:
            fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(20, 6))
            ax1 = cast(mpl_axes.Axes, ax1)
            ax2 = cast(mpl_axes.Axes, ax2)

            # Class pie chart
            ax1.pie(
                sorted_class_values,
                labels=sorted_class_labels,
                autopct='%1.1f%%',
                startangle=140,
                colors=[color_map[v] for v in sorted_class_labels],
            )
            ax1.axis('equal')
            ax1.set_title(f"{var_name} - Class File")

            # Nonclass pie chart
            ax2.pie(
                sorted_nonclass_values,
                labels=sorted_nonclass_labels,
                autopct='%1.1f%%',
                startangle=140,
                colors=[color_map[v] for v in sorted_nonclass_labels],
            )
            ax2.axis('equal')
            ax2.set_title(f"{var_name} - Nonclass File")

            save_path = os.path.join(graphs_dir, f"{var_name}.png")
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            plt.close(fig)

        except ValueError as ex:
            termcolor.cprint(f"Value error occurred while pie chart plotting for {var_name}.\nException: {ex}",
                "light_red", file=sys.stderr)

def generate_bar_graph(context: CFDContext) -> None:

    """
    Generates a bar graph showing the number of t-way interactions for each variable.
    The graph is saved in the Graphs subdirectory.
    NOTE: A high number of variables may result in crowded labels. As such, the
    information is also saved in a CSV file for easier viewing.
    """

    data = context.data
    variable_names = context.variable_names
    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff
    max_ways = context.max_t_ways
    output = context.output_path

    sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    graphs_dir = os.path.join(sub_dir_name, "Graphs")
    os.makedirs(graphs_dir, exist_ok=True)

    csv_file_name = f"bar_{class_file_name}_{nonclass_file_name}_{distinguishability_cutoff}.csv"
    csv_file_path = os.path.join(graphs_dir, csv_file_name)
    with open(csv_file_path, 'w') as csv_file:
        ways_str = ";".join(f"{t}-way" for t in range(1, max_ways+1))
        header = f"Feature;{ways_str}\n"
        csv_file.write(header)
        for i in range(len(variable_names)):
            counts = [cast(list[dict[str, int]], data[f'count{j+1}'])[i] for j in range(max_ways)]
            csv_file.write(f"{variable_names[i]};{';'.join(map(str, counts))}\n")

    count_lists = [np.array(data[f'count{i+1}']) for i in range(max_ways)]
    total_counts = sum(count_lists)

    if type(total_counts) is not np.ndarray:
        print_warning_message(context, "No t-way interactions found. Bar graph will not be generated")
        return

    # Sort variables by total count
    sorted_indices = np.argsort(total_counts)
    variables = np.arange(len(variable_names))
    width = 0.5

    fig, ax = plt.subplots()
    bottoms = np.zeros_like(count_lists[0])
    colors = ['red', 'blue', 'green', 'orange', 'purple', 'teal']

    for i, counts in enumerate(count_lists):
        color = colors[i % len(colors)]
        current = counts[sorted_indices]
        ax.bar(
            variables,
            current,
            width,
            bottom=bottoms[sorted_indices],
            label=f"{i+1}-way",
            color=color
        )

        # Position each label above the top of the full bar stack (staggered to avoid collisions)
        for j, var_idx in enumerate(sorted_indices):
            val = counts[var_idx]
            stacked_height = sum(counts_k[var_idx] for counts_k in count_lists[:max_ways])
            offset = total_counts.max() * 0.04 * (i)
            ax.text(
                j,
                stacked_height + offset,
                str(val),
                ha='center',
                va='bottom',
                fontsize=7,
                color=color
            )

        bottoms += counts

    y_upper_limit = total_counts[sorted_indices].max() * 1.3
    ax.set_ylim(0, y_upper_limit)
    ax.set_ylabel('Number of Interactions')
    ax.set_title('Number of T-way Interactions in DVCs for Each Feature')

    ax.set_xticks(variables)
    rotated_names = np.array(variable_names)[sorted_indices]
    ax.set_xticklabels(rotated_names, rotation=90, ha='center')

    ax.legend(loc='upper left')
    plt.subplots_adjust(bottom=0.25)
    plt.tight_layout()

    file_name = os.path.join(graphs_dir, "feature_bar_graph.png")
    plt.savefig(file_name, dpi=300, bbox_inches='tight')
    plt.close(fig)

def get_missing_value_combinations(context: CFDContext) -> None:

    """
    Generates and saves the missing value combinations (MVCs) for each t-way interaction level.
    This function creates a directory for MVCs and writes the missing combinations
    for each t-way interaction into separate text files.
    NOTE: This function can be time-consuming for large datasets, as it checks
    all combinations of values for each variable at the specified t-way level.
    """

    distinguishability_cutoff = context.distinguishability_cutoff
    variable_names = context.variable_names
    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    max_ways = context.max_t_ways
    output = context.output_path
    logs = context.logs
    silent = context.silenced or context.silenced_ts
    missing_tway_combos = context.missing_tway_combos
    missing_internal = context.missing_internally_all_tways

    if max_ways == 1:
        # There are no MVCs for only 1-way interactions
        print_warning_message(context, "No missing value combinations can be generated for 1-way interactions")
        return

    print_timestamp_message(context, "Starting MVC file generation")

    sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    MVCs_dir = os.path.join(sub_dir_name, "MVCs")
    os.makedirs(MVCs_dir, exist_ok=True)

    def write_mvc_file(hide_bar: bool, st: float, t: int) -> bool:
        new_file_name = f"{t}-way-MVCs.csv"
        file_path = os.path.join(MVCs_dir, new_file_name)
        header = "File;Internal_Class;Internal_Nonclass"
        for i in range(t):
            header +=f";Feature_Value_{i+1}"
        key = f'{t}-way'
        with open(file_path, "w") as file:
            MVC_class_file = missing_tway_combos[key][0]
            MVC_nonclass_file = missing_tway_combos[key][1]
            MVC_union_file = missing_tway_combos[key][2]
            with tq(total=len(MVC_class_file) + len(MVC_nonclass_file) + len(MVC_union_file), 
                    desc=f"{t}-way MVCs", disable=hide_bar) as pbar:
                file.write(f"{header}\n")
                for elem in MVC_union_file:
                    if st != 0 and time.time() > st + 3:
                        file.close()
                        return False
                    pbar.update(1)
                    combo = tuple(zip(tuple(elem[1]), elem[0]))
                    int_cl, int_nc = missing_internal[key][combo]
                    elem_lst = [(variable_names[elem[1][i]], elem[0][i]) for i in range(t)]
                    elem_str = ";".join([f"({var}, {val})" for var, val in elem_lst])
                    file.write(f"Both;{int_cl};{int_nc};{elem_str}\n")
                for elem in MVC_class_file:
                    if st != 0 and time.time() > st + 3:
                        file.close()
                        return False
                    pbar.update(1)
                    combo = tuple(zip(tuple(elem[1]), elem[0]))
                    int_cl, int_nc = missing_internal[key][combo]
                    elem_lst = [(variable_names[elem[1][i]], elem[0][i]) for i in range(t)]
                    elem_str = ";".join([f"({var}, {val})" for var, val in elem_lst])
                    file.write(f"Class;{int_cl};{int_nc};{elem_str}\n")
                for elem in MVC_nonclass_file:
                    if st != 0 and time.time() > st + 3:
                        file.close()
                        return False
                    pbar.update(1)
                    combo = tuple(zip(tuple(elem[1]), elem[0]))
                    int_cl, int_nc = missing_internal[key][combo]
                    elem_lst = [(variable_names[elem[1][i]], elem[0][i]) for i in range(t)]
                    elem_str = ";".join([f"({var}, {val})" for var, val in elem_lst])
                    file.write(f"Nonclass;{int_cl};{int_nc};{elem_str}\n")
        file.close()
        return True

    for t in range(2, max_ways+1):
        if logs and not silent:
            if not write_mvc_file(True, time.time(), t):
                write_mvc_file(False, 0, t)
        else:
            write_mvc_file(True, 0, t)
 
def download_DVCs(context: CFDContext) -> None:

    """
    Generates and saves DVC CSV files for each t-way interaction level to 
    a newly created subdirectory.
    """

    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff
    max_ways = context.max_t_ways
    logs = context.logs
    silent = context.silenced or context.silenced_ts
    output = context.output_path
    csv_dvc_print_tway = context.csv_dvc_print_tway

    sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    dvcs_dir = os.path.join(sub_dir_name, "DVCs")
    os.makedirs(dvcs_dir, exist_ok=True)

    def write_dvcs(hide_bar: bool, timeout: bool, t: int) -> bool:
        st = time.time()
        var_lst = [f"Variable{i}" for i in range(1,t+1)]
        var_str = ";".join(var_lst)
        header_str = f"Type;Class;{var_str};Frequency;Frequency_Difference;\n"
        entries_list = csv_dvc_print_tway[t]
        new_file_name = f"{t}-way_DVCs.csv"
        file_path = os.path.join(dvcs_dir, new_file_name)

        with open(file_path, "w") as file:
            file.write(header_str)
            with tq(total=len(entries_list), desc=f"{t}-way DVCs", disable=hide_bar) as pbar:
                for entry in entries_list:
                    file.write(f"{entry}\n")
                    pbar.update(1)
                    if timeout and time.time() - st > 3:
                        file.close()
                        return False
        file.close()
        return True

    for t in range(1,max_ways+1):
        print_timestamp_message(context, f"Generating {t}-way DVC file")
        if logs and not silent:
            if not write_dvcs(True, True, t):
                write_dvcs(False, False, t)
        else:
            write_dvcs(True, False, t)

def download_info(context: CFDContext) -> None:

    """
    Generates an information file summarizing the results of the CFD analysis.
    """

    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    data = context.data
    distinguishability_cutoff = context.distinguishability_cutoff
    class_file_duplicates = context.class_file_duplicates
    nonclass_file_duplicates = context.nonclass_file_duplicates
    ncc = context.ncc
    nrc = context.nrc
    nrn = context.nrn
    has_header = context.has_header
    common_entries = context.common_entries
    drop_common = context.drop_common
    avg_val_per_var = context.avg_val_per_var
    variable_names = context.variable_names
    max_ways = context.max_t_ways
    col_drop = context.col_drop
    dropped_columns = context.column_names_dropped
    auto_remove_dups = context.remove_dups
    output = context.output_path
    filter = context.filter
    feature_bins = context.feature_bin_ranges
    gen_mvcs = context.gen_mvcs
    missing = context.missing_tway_combos
    missing_counts = context.missing_internal_counts

    grid = cast(list[list[int]], data['grid'])
    common_entries = cast(list[tuple[tuple[str], dict[str,int]]], data['common_entries'])

    sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    os.makedirs(sub_dir_name, exist_ok=True)
    new_file_name = f"info.txt"
    file_path = os.path.join(sub_dir_name, new_file_name)

    disclaimer = """
Disclaimer: Research Prototype Tool

This tool is provided as a research prototype and is intended for experimental and informational purposes only. 
Users are advised that the tool may produce inaccurate or incomplete information and may contain unknown bugs or errors.
The results generated by the tool should be treated with caution and should not be relied upon as the sole basis \
for decision-making in critical settings.
Users are strongly encouraged to validate the tool's output before making any critical decisions.
The developers and providers of this tool shall not be held responsible for any consequences arising from the \
use of its results without proper validation or for any actions taken based on the tool's output.

By using this tool, you acknowledge and accept these inherent limitations and uncertainties, and agree to exercise \
due diligence in verifying its results prior to implementation in important contexts.
"""

    today_date = datetime.now().strftime('%Y-%m-%d')
    var_names = ', '.join(str(name) for name in variable_names)

    with open(file_path, "w") as file:
        file.write(disclaimer)
        file.write("\n")
        file.write(f"Today's date: {today_date}\n")
        file.write(f"T-level specified: {max_ways}\n")
        file.write(f"Class file: {class_file_name}\n")
        file.write(f"Nonclass file: {nonclass_file_name}\n")
        file.write(f"Number of class rows: {nrc}\n")
        file.write(f"Number of nonclass rows: {nrn}\n\n")

        if not dropped_columns:
            file.write(f"No columns were automatically dropped\n\n")
            file.write(f"Number of variables: {ncc}\n")
        else:
            plural = "columns were" if len(dropped_columns) > 1 else "column was"
            file.write(f"{len(dropped_columns)} {plural} automatically dropped:")
            cols = '\t'.join(dropped_columns)
            file.write(f"{cols}\n\n")
            file.write(f"Number of variables remaining: {ncc}\n")
        if has_header:
            file.write(var_names + '\n')

        file.write("\n")
        aft_bin = "There"
        if feature_bins:
            aft_bin = "After binning, there"
            plural = "features were" if len(feature_bins) > 1 else "feature was"
            file.write(f"{len(feature_bins)} {plural} binned:\n")
            padding = [max(len(f[0]) for f in feature_bins), max(len(str(f[1])) for f in feature_bins), 
                       max(len(str(len(f[2]))) for f in feature_bins)]
            for tup in feature_bins:
                range_as_strs_list = [(str(round(a, 6)), str(round(b, 6))) for a, b in tup[2]]
                range_as_strs_list[0] = ('-inf', range_as_strs_list[0][1])
                range_as_strs_list[-1] = (range_as_strs_list[-1][0], 'inf')
                ranges_str = ', '.join(f'{a, b}' for (a, b) in range_as_strs_list)
                ranges_str = ranges_str.replace(')', ']', ranges_str.count(')') - 1)
                ranges_str = ranges_str.replace('\'', '')
                file.write(f"{tup[0]:<{padding[0]}} ({tup[1]:<{padding[1]}} values down to " \
                           f"{str(len(tup[2])):<{padding[2]}}): {ranges_str}\n")
        else:
            file.write("No features were binned\n")
        file.write("\n")
        file.write(f"{aft_bin} are {data['num_diff_values']} different values taken on by these variables, " \
                   f"with an average of {avg_val_per_var:.3f} values per variable.\n")
        plural_1 = "are" if cast(int, data['num_intersect_vals']) != 1 else "is"
        plural_2 = "are" if cast(int, data['num_uniq_vals_class']) != 1 else "is"
        plural_3 = "are" if cast(int, data['num_uniq_vals_nonclass']) != 1 else "is"

        file.write(f"{data['num_intersect_vals']} of these values {plural_1} present in both files.\n")
        file.write(f"{data['num_uniq_vals_class']} {plural_2} only present in the class file.\n")
        file.write(f"{data['num_uniq_vals_nonclass']} {plural_3} only present in the nonclass file.\n\n")

        len_common = len(common_entries)
        if len_common > 0:
            plural = "entries" if len_common > 1 else "entry"
            file.write(f"{len_common} {plural} appeared in both files:\n")
            for _, entry in zip(range(3), common_entries, strict=False):
                entry_values, counts = entry[0], entry[1]
                class_count = counts['class_count']
                nonclass_count = counts['nonclass_count']
                file.write(f"Entry: {entry_values}:\nClass Count: {class_count}, Nonclass Count: {nonclass_count}\n\n")
            if len(common_entries) > 3:
                file.write(f"To view all {len_common} {plural}, check common_entries.csv\n")
                if drop_common != 'none':
                    which_file_s = 'the class file' if drop_common == 'class' else 'the nonclass file'
                    which_file_s = 'both the class and nonclass files' if drop_common in ['all', 'both'] else which_file_s 
                    file.write(f"All common entries were removed from {which_file_s}.\n\n")
        else:
            file.write("No entries appeared in both files.\n\n")

        if class_file_duplicates:
            plural = "rows were" if len(class_file_duplicates) > 1 else "row was"
            file.write(f"{len(class_file_duplicates)} duplicate {plural} detected in the class file.\n")
            with open(os.path.join(sub_dir_name, f"{class_file_name}_duplicates.csv"), "w") as class_dup_file:
                class_dup_file.write(";".join(str(value) for value in context.variable_names) + "\n")
                for row in class_file_duplicates:
                    class_dup_file.write(";".join(value for value in row) + "\n")
        else:
            file.write("No duplicate rows were detected in the class file.\n")

        if nonclass_file_duplicates:
            plural = "rows were" if len(nonclass_file_duplicates) > 1 else "row was"
            file.write(f"{len(nonclass_file_duplicates)} duplicate {plural} detected in the nonclass file.\n")
            with open(os.path.join(sub_dir_name, f"{nonclass_file_name}_duplicates.csv"), "w") as nonclass_dup_file:
                nonclass_dup_file.write(";".join(str(value) for value in context.variable_names) + "\n")
                for row in nonclass_file_duplicates:
                    nonclass_dup_file.write(";".join(str(value) for value in row) + "\n")
        else:
            file.write("No duplicate rows were detected in the nonclass file.\n")

        num_dups = len(class_file_duplicates) + len(nonclass_file_duplicates)
        if auto_remove_dups and num_dups > 0:
            plural = "rows were" if num_dups > 1 else "row was"
            file.write(f"The duplicate {plural} removed before processing\n")

        if filter:
            file.write("\nThe filter was enabled. T-way DVCs which contain a lower level t-way DVC are " \
                       "not themselves also considered DVCs.\n")
        else:
            file.write("\nThe filter was not enabled. T-way DVCs which contain a lower t-level DVC still qualify.\n")
        file.write("\n")
        for t in range(max_ways):
            file.write(f"\nAt t-level {t+1} there are:\n")
            file.write(f" * Maximum Value Interactions:               {grid[t][0]}\n")
            file.write(f" * Maximum Class Value Interactions:         {grid[t][1]}\n")
            file.write(f" * Maximum Nonclass Value Interactions:      {grid[t][2]}\n")
            file.write(f" * Present Class Value Interactions:         {grid[t][3]}\n")
            file.write(f" * Present Nonclass Value Interactions:      {grid[t][4]}\n")
            file.write(f" * Value Combinations Present in Both:       {grid[t][5]}\n")
            file.write(f" * Distinguishing Value Combinations:        {grid[t][6]}\n")
            file.write(f" * Percent of All DVCs:                      {grid[t][7]}\n")
            file.write(f" * Number of DVC Occurrences:                {grid[t][8]}\n")
            file.write(f" * Percent of All DVC Occurrences:           {grid[t][9]}\n")
            if gen_mvcs and t >= 1:
                key = f'{t+1}-way'
                largest = 0
                plural = ["were"] * 12
                for i in range(12):
                    c = missing_counts[key][i]
                    if c == 1:
                        plural[i] = "was"
                    if c > largest:
                        largest = c
                buffer = len(str(largest))
                file.write(f" * VCs absent solely from the class file:    {len(missing[key][0])}\n")
                file.write(f"   * {missing_counts[key][0]:>{buffer}d} of which {plural[0]} possible with only values present in either file independently.\n")
                file.write(f"   * {missing_counts[key][1]:>{buffer}d} of which {plural[1]} only possible with values only present in the class file.\n")
                file.write(f"   * {missing_counts[key][2]:>{buffer}d} of which {plural[2]} only possible with values only present in the nonclass file.\n")
                file.write(f" * VCs absent solely from the nonclass file: {len(missing[key][1])}\n")
                file.write(f"   * {missing_counts[key][4]:>{buffer}d} of which {plural[4]} possible with only values present in either file independently.\n")
                file.write(f"   * {missing_counts[key][5]:>{buffer}d} of which {plural[5]} only possible with values only present in the class file.\n")
                file.write(f"   * {missing_counts[key][6]:>{buffer}d} of which {plural[6]} only possible with values only present in the nonclass file.\n")
                file.write(f" * VCs absent from both files:               {len(missing[key][2])}\n")
                file.write(f"   * {missing_counts[key][8]:>{buffer}d} of which {plural[8]} possible with only values present in either file independently.\n")
                file.write(f"   * {missing_counts[key][9]:>{buffer}d} of which {plural[9]} only possible with values present in the class file.\n")
                file.write(f"   * {missing_counts[key][10]:>{buffer}d} of which {plural[10]} only possible with values present in the nonclass file.\n")
                file.write("\n")
        file.close()

def get_filename_limit() -> int:

    """
    Return the maximum file name / folder path length of the user's system. Typically 255.
    """

    try:
        return os.pathconf('.', 'PC_NAME_MAX') # type: ignore
    except Exception:
        return 255

def sanitize_values(context: CFDContext) -> None:
    class_file_data = context.class_file_data
    nonclass_file_data = context.nonclass_file_data
    ncc = context.ncc

    before = ""
    after = ""
    class_new_vals: set[str] = set()
    for row in class_file_data:
        for i in range(ncc):
            before = row[i]
            row[i] = re.sub(r'[^\x00-\x7F]+', '_', row[i])
            after = row[i]
            if before != after and after not in class_new_vals:
                class_new_vals.add(after)
                print_warning_message(context, f"A value in the class file has been converted from {before} to {after}", 
                    do_not_write=True)
    nonclass_new_vals: set[str] = set()
    for row in nonclass_file_data:
        for i in range(ncc):
            before = row[i]
            row[i] = re.sub(r'[^\x00-\x7F]+', '_', row[i])
            after = row[i]
            if before != after and after not in nonclass_new_vals:
                nonclass_new_vals.add(after)
                print_warning_message(context, f"A value in the nonclass file has been converted from {before} to {after}", 
                    do_not_write=True)

def sanitize_name(name: str, replacement: str='_', file: str='') -> str:

    """
    Replaces or removes characters unsafe for filenames / variable names
    Also collapses repeated separators and trims leading/trailing separators.
    """

    # Replace unsafe characters with the replacement character
    name = re.sub(r'[<\'>\f:"\t,\b;&/\\|\r?*\n]', replacement, name)
    # Replace non-ascii characters with the replacement character
    name = re.sub(r'[^\x00-\x7F]+', replacement, name)

    # Collapse multiple replacement characters (ex, "__" -> "_")
    name = re.sub(rf'{re.escape(replacement)}+', replacement, name)

    final = name.strip(replacement + ". ")
    if final == "" and file != '': # If we're sanitizing a file parameter name to nothing
        final = f"{file}file" # Then make it classfile / nonclassfile as appropriate rather than _.csv
    return final

class CustomArgumentParser(argparse.ArgumentParser):

    """
    Custom argument parser that overrides the default error handling
    to provide a more user-friendly error message.
    """

    def error(self, message):
        self.print_usage(sys.stderr)
        termcolor.cprint(f"\nError: {message}\n", "red", attrs=['bold'])
        print("You must at a minimum provide a path to your [class_file], your [nonclass_file], " \
              "and your [distinguishing cutoff].\n")
        print("For more information, please refer to the CFD Command Line Guide manual or call --help\n")
        sys.exit(1)

def parse_args() -> CFDContext:

    """
    Parse all command line arguments and create the Context object which will store them, among other data
    """

    parser = CustomArgumentParser(
        description="Combination Frequency Differencing Tool (CFD) Command Line Interface (CLI) Version 1.1.0",
        epilog="For more information, please refer to the CFD Command Line Guide.\n"
    )
    parser.add_argument(
        "class_file",
        help="Path to the class file (CSV format)"
    )
    parser.add_argument(
        "nonclass_file",
        help="Path to the nonclass file (CSV format)"
    )
    parser.add_argument(
        "distinguishability_cutoff",
        type=float,
        help="Threshold multiplier for distinguishing combinations"
    )
    parser.add_argument(
        "-v", "--verbose", "--v", "--verb",
        action="store_true",
        default=False,
        help="Enable verbose output when data file(s) have a header row with variable names",
        dest='v'
    )
    parser.add_argument(
        "-l", "--l", "--log", "--logs",
        action="store_true",
        default=False,
        help="Log program execution (timestamps, info outputs) to a log file and the terminal",
        dest='l'
    )
    parser.add_argument(
        "-o", "--o", "--ow", "--overwrite",
        action="store_true",
        default=False,
        help="Always overwrite old files and graphs when rerunning data with the same parameters",
        dest='o'
    )
    parser.add_argument(
        "-m" , "--m", "--mvc", "--mvcs", "--missing",
        action="store_true",
        default=False,
        help="Generate missing value combinations (MVCs) for each t-way interaction level and save them to csv files",
        dest='m'
    )
    parser.add_argument(
        "-g", "--g", "--graph", "--graphs",
        action="store_true",
        default=False,
        help="Generate graphs and diagrams for t-way interactions and save them to a subdirectory",
        dest='g'
    )
    parser.add_argument(
        "-r", "--r", "--rd", "--remove", "--remove_duplicates",
        action="store_true",
        default=False,
        help="Always remove duplicate rows from class and nonclass files without prompting",
        dest='r'
    )
    parser.add_argument(
        "-t", "--t", "--tway", "--max", "--max-t", "--max-ways",
        type=int, 
        default=3,
        choices=[1,2,3,4,5,6],
        help="Max level of t-way combinations which will be calculated (default: 3, range: 1-6 inclusive)",
        dest='t'
    )
    parser.add_argument(
        "-c", "--c", "--complete", "--complete_rows",
        action="store_true",
        default=False,
        help="Always remove rows with missing data from class and nonclass files without prompting",
        dest='c'
    )
    parser.add_argument(
        "-d", "-s", "--d", "--s", "--delim", "--delimiter", "--sep", "--separator",
        type=str,
        default=",",
        help="Specify a special delimiter for your CSV files (default: comma)",
        dest='d'
    )
    parser.add_argument(
        "--silent", "--silence",
        nargs='?',
        type=str,
        default='none',
        const='all',
        choices=['none', 'ts', 'info', 'all', 'both', ''],
        help="Silence all program output to the terminal except for errors and user prompts.\n" \
             "Alternatively, specify \'--silent info\' or \'--silent ts\' to silence only info or " \
             "timestamp statements to terminal respectively",
        dest='silent'
    )
    parser.add_argument(
        "--drop", "--autodrop", "--recdrop",
        nargs='?',
        type=str,
        default='NONE',
        const='',
        choices=['', 'auto', 'all'],
        help="Be prompted whether to drop columns from the class and nonclass files if the tool recommends it. " \
             "Original files will not be affected. Use '--drop auto' to always drop columns which cannot assist " \
             "in file differentiation. Use '--drop all' to drop all columns which may be wrongly included",
        dest='drop'
    )
    parser.add_argument(
        "-f", "--filter", "--filter-on",
        action="store_true",
        default=False,
        help="Filter out lower level t-way DVCs from higher level t-way DVCs",
        dest='f'
    )
    parser.add_argument(
        "--force",
        action="store_true",
        default=False,
        help="Force through some of the error checks. DO NOT USE UNLESS CERTAIN",
        dest="force"
    )
    parser.add_argument(
        "--bin",
        nargs='?',
        action='append',
        default=[],
        choices=['manual','auto','automatic','width','freq','frequency','none', 'all', 'none'] + [str(i) for i in range(1, 101)],
        const='manual',
        help="When a feature is determined to be continuous, gain the ability to bin it before proceeding. By default, " \
             "multiple options will be displayed with the ability to see different binning configurations. " \
             "Alternatively, specify \'--bin auto\' to always use the recommended number and placement of bins (experimental). " \
             "Alternatively and/or additionally, optionally specify \'--bin width\' or \'--bin freq\' to bin by equal " \
             "width or equal frequency instead of the best bin placement estimation. Optionally, further specify \'--bin #\' " \
             "to always bin with a set number of bins (1-100 supported) for each feature determined to be continuous. " \
             "If a number is provided, optionally further append \'--bin all\' to bin all features with that " \
             "many bins, if able, instead of just features determined to be continuous. Lastly, you may specify " \
             "\'--bin none\' to disable the continuous variable check" ,
        dest='bin'
    )
    parser.add_argument(
        '--out', '--output',
        nargs='?',
        const='output',
        default='output',
        help='Specify an output folder for results. Default: "output"',
        dest='output'
    )
    parser.add_argument(
        '--drop-common', '--no-common', '--nce', '--dce',
        nargs='?',
        const='all',
        default='none',
        choices=['all', 'both', 'class', 'nonclass', 'none', ''],
        help='Enable to drop all common entries from one or both files (--nce, --nce class, --nce nonclass)',
        dest='drop_common'
    )
    
    args = parser.parse_args()

    context = CFDContext()
    context.remove_dups = args.r
    context.overwrite = args.o
    context.complete_rows_only = args.c
    context.verbose = args.v
    context.logs = args.l
    context.gen_mvcs = args.m
    context.gen_graphs = args.g
    context.max_t_ways = args.t
    context.delimiter = args.d
    context.filter = args.f
    context.silenced = True if (args.silent).lower() == 'all' or (args.silent).lower() == 'both' else False
    context.silenced_info = True if (args.silent).lower() == 'info' else False
    context.silenced_ts = True if (args.silent).lower() == 'ts' else False
    context.col_drop = args.drop
    context.force = args.force
    context.all_bin_params = args.bin
    context.output_path = args.output
    context.drop_common = args.drop_common
    context.class_file_path = sys.argv[1]
    context.nonclass_file_path = sys.argv[2]
    context.distinguishability_cutoff = float(sys.argv[3])
    return context

def check_bin_params(context: CFDContext, params: list[str]) -> None:

    """
    Verify that all the user specified binning parameters are compatible, then assign variables accordingly.
    """

    if 'none' in params and len(params) > 1:
        print_warning_message(context, "If not binning, you cannot specify further binning options", True)
    if ('freq' in params or 'frequency' in params) and 'width' in params:
        print_warning_message(context, "Binning by width and frequency are mutually incompatible", True)
    if 'manual' in params and ('auto' in params or 'automatic' in params):
        print_warning_message(context, "Binning manually and automatically are mutually incompatible", True)

    num_ints = 0
    spec_num = -1
    for el in params:
        try:
            spec_num = int(el)
            num_ints += 1
        except:
            pass
    if num_ints > 1:
        print_warning_message(context, "Only up to one number of bins for all features can be specified", True)

    if num_ints == 1 and 'manual' in params:
        print_warning_message(context, "Specifying a set number of bins is typically done to modify auto-binning " \
            "behavior, however you have specified manual binning. Only the specified number of bins will be calculated")

    # Now assign all variables
    if 'freq' in params or 'frequency' in params:
        context.bin_by_freq = True
    elif 'width' in params:
        context.bin_by_width = True
    else:
        context.bin_by_estimate = True
    if 'none' in params or not params:
        context.do_not_bin = True
    if 'auto' in params or 'automatic' in params:
        context.auto_bin = True
    if spec_num != -1:
        context.set_bin_num = spec_num
    if 'all' in params:
        context.bin_all_vars = True
    return

def main(context: CFDContext) -> None:
    class_file_path = context.class_file_path
    nonclass_file_path = context.nonclass_file_path
    distinguishability_cutoff = context.distinguishability_cutoff
    max_t_ways = context.max_t_ways
    gen_mvcs = context.gen_mvcs
    gen_graphs = context.gen_graphs

    check_bin_params(context, context.all_bin_params)
    class_file_name, _ = os.path.splitext(os.path.basename(class_file_path))
    nonclass_file_name, _ = os.path.splitext(os.path.basename(nonclass_file_path))
    context.class_file_name = class_file_name = sanitize_name(class_file_name, file='class')
    context.nonclass_file_name = nonclass_file_name = sanitize_name(nonclass_file_name, file='nonclass')
    max_t_ways = cast(int, max_t_ways)

    max_name_length = get_filename_limit()
    if len(class_file_name) + len(nonclass_file_name) + 20 > max_name_length:
        if context.force:
            print_warning_message(context, "Force has bypassed file path length restriction")
        else:
            print_warning_message(context, "Your class and nonclass file names, when combined, will approach or exceed " \
                "the limit of your system for file name/path lengths (typically 255). Please use shorter file names", True, True)

    if class_file_name == nonclass_file_name:
        nonclass_file_name += "_nc"
        context.nonclass_file_name = nonclass_file_name
        print_warning_message(context, "The class and nonclass file names are the same. " \
            "Nonclass file name will be suffixed with '_nc'")

    if max_t_ways > 6 or max_t_ways < 1:
        print_warning_message(context, "Please choose an int value for max t-ways between 1-6 inclusive", True)

    if distinguishability_cutoff <= 1:
        print_warning_message(context, "The distinguishability cutoff must be a real number greater than 1 " \
            f"(Currently {distinguishability_cutoff})", True)

    get_set_files(context)

    ncc = context.ncc
    if max_t_ways > ncc:
        print_warning_message(context, f"You are trying to get {max_t_ways}-way data despite only having {ncc} variables", True)

    run_data(context)
    grid = cast(list[list[int]], context.data['grid'])
    missing_counts = context.missing_internal_counts

    def assert_ge(context: CFDContext, a: float, b: float, description: str="", only_equals=False) -> None:

        """
        Asserts that a is greater than or equal to b. If it isn't, a custom error message is displayed.
        """

        comp = ">="
        try:
            if only_equals:
                comp = "=="
                assert a == b
            else:
                assert a >= b
        except AssertionError:
            print_warning_message(context, f"Assertion failed: {a} {comp} {b} was False. {description}", True)

    for i in range(max_t_ways):
        grid_i0 = grid[i][0]
        grid_i1 = grid[i][1]
        grid_i2 = grid[i][2]
        grid_i3 = grid[i][3]
        grid_i4 = grid[i][4]
        grid_i5 = grid[i][5]
        grid_i6 = grid[i][6]

        assert_ge(context, grid_i0, grid_i1,
                f"Max Possible {i}-way VI >= Max Possible {i}-way Class VI")
        assert_ge(context, grid_i0, grid_i2,
                f"Max Possible {i}-way VI >= Max Possible {i}-way Nonclass VI")
        assert_ge(context, grid_i0, grid_i3,
                f"Max Possible {i}-wayVI >= Present {i}-wayClass VI")
        assert_ge(context, grid_i0, grid_i4,
                f"Max Possible {i}-way VI >= Present {i}-way Nonclass VI")
        assert_ge(context, grid_i0, grid_i5,
                f"Max Possible {i}-way VI >= Present {i}-way Intersect VI")
        assert_ge(context, grid_i0, grid_i6,
                f"Max Possible {i}-way VI >= Distinguishing {i}-way VI")
        assert_ge(context, grid_i1, grid_i3,
                f"Max Possible {i}-way Class VI >= Present {i}-way Class VI")
        assert_ge(context, grid_i1, grid_i5,
                f"Max Possible {i}-way Class VI >= Present {i}-way Intersect VI")
        assert_ge(context, grid_i2, grid_i4,
                f"Max Possible {i}-way Nonclass VI >= Present {i}-way Nonclass VI")
        assert_ge(context, grid_i2, grid_i5,
                f"Max Possible {i}-way Nonclass VI >= Present {i}-way Intersect VI")
        assert_ge(context, grid_i3, grid_i5,
                f"Present {i}-way Class VI >= Present {i}-way Intersect VI")
        assert_ge(context, grid_i4, grid_i5,
                f"Present {i}-way Nonclass VI >= Present {i}-way Intersect VI")

    if gen_mvcs:
        for t in range(2, max_t_ways+1):
            class_indices = [0, 1, 8, 9]
            nonclass_indices = [4, 6, 8, 10]
            class_missing = sum([missing_counts[f'{t}-way'][i] for i in class_indices])
            nonclass_missing = sum([missing_counts[f'{t}-way'][i] for i in nonclass_indices])
            assert_ge(context, grid[t-1][1], grid[t-1][3] + class_missing, 
                f"Max Possible {t}-way Class VI == Present Class {t}-way VI ({grid[t-1][3]}) + Missing Class {t}-way VI", True)
            assert_ge(context, grid[t-1][2], grid[t-1][4] + nonclass_missing,
                f"Max Possible {t}-way Nonclass VI == Present Nonclass {t}-way VI ({grid[t-1][4]}) + " \
                f"Missing Nonclass {t}-way VI", True)

    # Validation done, values obtained make mathematical sense (ie, max possible tways >= present tways, etc).
    # NOTE This does not guarantee correctness of the data, however.

    print_timestamp_message(context, "Starting info file generation")
    download_info(context)

    print_timestamp_message(context, "Starting DVC file generation")
    download_DVCs(context)

    if gen_mvcs:
        get_missing_value_combinations(context)

    if gen_graphs:
        print_timestamp_message(context, "Starting Graphs - Bar")
        generate_bar_graph(context)

        print_timestamp_message(context, "Starting Graphs - Pie")
        generate_pie_charts(context)

        print_timestamp_message(context, "Starting Graphs - Venn")
        generate_venn_diagram_graph(context)

    print_timestamp_message(context, "Starting t-way combinatorial coverage graphs")
    get_tway_coverage_graphs(context)
    print_timestamp_message(context, "Generating DVC counts per row CSVs")
    generate_DVC_occurrences_CSVs(context)
    print_timestamp_message(context, f"Output files generated (program is complete)")

    if context.num_warnings >= 1:
        plural = "warnings were" if context.num_warnings > 1 else "warning was"
        print_warning_message(context, f"{context.num_warnings} {plural} generated during program execution")

    now = datetime.now()
    elapsed = now - context.start_time
    total_seconds = int(elapsed.total_seconds())
    hours = total_seconds // 3600
    minutes = (total_seconds % 3600) // 60
    seconds = total_seconds % 60
    print_info_message(context, f"Total runtime: {hours} hours, {minutes} minutes, and {seconds} seconds")

def print_timestamp_message(context: CFDContext, message: str) -> None:

    """ 
    If logs are enabled, prints a timestamped message to the console and write it to the log file.
    """

    if not context.logs:
        return

    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff
    output = context.output_path

    now = datetime.now()
    formatted_time = now.strftime("%H:%M:%S")
    if not (context.silenced or context.silenced_ts):
        termcolor.cprint(f"TS: {message} - {formatted_time}", "green")

    sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    os.makedirs(sub_dir_name, exist_ok=True)
    new_file_name = f"logs.txt"
    file_path = os.path.join(sub_dir_name, new_file_name)
    with open(file_path, "a") as file:
        file.write(f"TS: {message} - {formatted_time}\n")
        file.close()

def detect_header(df: pd.DataFrame) -> bool:

    """
    Detects if the first row is a header based on whether any of its values appear elsewhere in their columns.
    This is not perfect, but is typically good enough.
    Info / Warning statements may indicate when this has gone wrong.
    """

    first_row = df.iloc[0]
    for column in df.columns:
        if first_row[column] in df[column].iloc[1:].values:
            return False
    return True

def remove_incomplete_rows(context: CFDContext, df: pd.DataFrame, is_class: bool) -> pd.DataFrame:

    """
    Removes rows with any missing values from the DataFrame.
    * If no incomplete rows are found, it returns the original DataFrame.
    * If incomplete rows are found, it prompts the user to either remove, keep, or display them.
    * If the user chooses to remove them, it returns a cleaned DataFrame without those rows.
    * If the user chooses to keep them, it returns the original DataFrame.
    * If the user chooses to display them, all rows with missing data will be displayed and the user will be re-prompted.
    * If the user chooses to exit, it terminates the program.
    """

    auto_remove = context.complete_rows_only
    logs = context.logs

    incomplete_mask = df.isnull().any(axis=1)
    incomplete_rows = df[incomplete_mask].copy()
    incomplete_rows_list = incomplete_rows.to_dict(orient='records')
    incomplete_rows = df[df.isnull().any(axis=1)]
    num_incomplete = len(incomplete_rows)

    if is_class:
        name = context.class_file_name
    else:
        name = context.nonclass_file_name

    if num_incomplete == 0:
        if logs:
            print_info_message(context, f"No incomplete rows found in {name}")
        return df

    plural = ("rows", "entries", "them") if num_incomplete != 1 else ("row", "entry", "it")
    print_info_message(context, f"Detected {num_incomplete} {plural[0]} with missing value(s) in {name}", not auto_remove)

    response = ""
    if auto_remove:
        response = "R"
    while response.upper() not in {"R", "K", "D", "X", "REMOVE", "KEEP", "DISPLAY", "EXIT"}:
        response = input(f"Would you like to (R)emove {plural[2]}, (K)eep {plural[2]}, (D)isplay {plural[2]}, or " \
                         "e(X)it the program?\n> ")
        if response.upper() == 'D' or response.upper() == "DISPLAY":
            print(f"Info: Incomplete {plural[1]} in {name}:\n")
            for row in incomplete_rows_list:
                print("\t".join(str(value) for value in row.values()))
            response = input(f"Would you like to (R)emove {plural[2]}, (K)eep {plural[2]}, or e(X)it the program?\n> ")

    if response.upper() == "R" or response.upper() == "REMOVE":
        df_cleaned = df.dropna()
        print_info_message(context, f"Removed {num_incomplete} incomplete {plural[0]} from {name}")
        return df_cleaned
    elif response.upper() == "K" or response.upper() == "KEEP":
        print_info_message(context, f"Keeping {num_incomplete} incomplete {plural[0]} in {name} as-is")
        return df
    else:
        sys.exit(0)

def remove_duplicate_rows(context: CFDContext) -> None:

    """
    Removes rows which appear multiple times in either the class or nonclass file.
    * If no duplicate rows are found, no changes are made.
    * If duplicate rows are found, it prompts the user to either remove, keep, or display them.
    * If the user chooses to remove them, all but the first instance of each duplicate row will be removed.
    * If the user chooses to keep them, no changes are made.
    * If the user chooses to display them, all duplicate rows will be displayed and the user will be re-prompted.
    * If the user chooses to exit, it terminates the program.
    """

    if context.remove_dups == False:
        return

    class_file_data = context.class_file_data
    nonclass_file_data = context.nonclass_file_data
    remove_dups = context.remove_dups
    logs = context.logs
    silent = context.silenced or context.silenced_ts

    def detect_dups(pbar: tq, start: float=0) -> tuple[bool, list[list[str]], list[list[str]]]:
        class_dups: list[list[str]] = []
        nonclass_dups: list[list[str]] = []
        unique_class: set[tuple[str, ...]] = set()
        unique_nonclass: set[tuple[str, ...]] = set()
        for row in class_file_data:
            if start != 0 and time.time() - start > 3:
                return False, [], []
            if tuple(row) in unique_class:
                class_dups.append(row)
            else:
                unique_class.add(tuple(row))
            pbar.update(1)
        for row in nonclass_file_data:
            if start != 0 and time.time() - start > 3:
                return False, [], []
            if tuple(row) in unique_nonclass:
                nonclass_dups.append(row)
            else:
                unique_nonclass.add(tuple(row))
            pbar.update(1)
        context.class_file_duplicates = class_dups
        context.nonclass_file_duplicates = nonclass_dups
        return True, class_dups, nonclass_dups

    pbar = tq(total=len(class_file_data)+len(nonclass_file_data), desc="Detecting Duplicate Rows", disable=True)
    if not silent:
        success, class_dups, nonclass_dups = detect_dups(pbar, time.time())
        if not success:
            pbar.close()
            pbar = tq(total=len(class_file_data)+len(nonclass_file_data), desc="Detecting Duplicate Rows")
            _, class_dups, nonclass_dups = detect_dups(pbar)
    else:
        _, class_dups, nonclass_dups = detect_dups(pbar)

    def remove_display_keep(dups: list[list[str]], file: str, data: list[list[str]]) -> list[list[str]] | None:
        if dups:
            response = ""
            and_rem = "and removed" if remove_dups else ""
            if remove_dups:
                response = "R"
            plural = ("rows", "entries", "them") if len(dups) != 1 else ("row", "entry", "it")
            print_info_message(context, f"Detected {and_rem} {len(dups)} duplicate {plural[0]} in {file}", not remove_dups)

            while response.upper() not in {"R", "K", "D", "X", "REMOVE", "KEEP", "DISPLAY", "EXIT"}:
                response = input(f"Would you like to (R)emove {plural[2]}, (K)eep {plural[2]}, (D)isplay {plural[2]}, or " \
                                 "e(X)it the program?\n> ")
                if response.upper() == 'D' or response.upper() == 'DISPLAY':
                    print(f"Info: Duplicate {plural[1]} in the {file} file:\n")
                    for row in dups:
                        print("\t".join(str(value) for value in row))
                    response = input(f"\nWould you like to (R)emove {plural[2]}, (K)eep {plural[2]}, or e(X)it the program?\n> ")
            if response.upper() == 'R' or response.upper() == "REMOVE":
                if not remove_dups:
                    print_info_message(context, f"Removed {len(dups)} duplicate {plural[0]} from the {file} file")
                save_first: set[tuple[str, ...]] = set()
                for row in data:
                    if row in dups and not tuple(row) in save_first:
                        del row
                    elif row in dups:
                        save_first.add(tuple(row))
                return data
            elif response.upper() == 'K' or response.upper() == "KEEP":
                return
            elif response.upper() == 'X' or response.upper() == "EXIT":
                sys.exit(0)
        else:
            if logs:
                print_info_message(context, f"No duplicate rows detected in the {file} file")
        return
    dat = remove_display_keep(class_dups, 'class', class_file_data)
    if dat is not None:
        context.class_file_data = dat
        context.nrc = len(dat)

    dat = remove_display_keep(nonclass_dups, 'nonclass', nonclass_file_data)
    if dat is not None:
        context.nonclass_file_data = dat
        context.nrn = len(dat)

def detect_possible_unintentionally_unique_variable_names(context: CFDContext) -> None:

    """
    Detects the presence of values within a column differentiated solely by whitespace.
    * Ex, " Yes " and "Yes". These will be treated as unique, however that may be unintentional due to a mistake in the 
    CSV. 
    Warn the user for each column which contains values which meet this critera in the class or nonclass file.
    \n
    Apply the same process for values differentiated solely by the presence of quotes (\' or \").
    """

    if context.force:
        return

    class_file_data = context.class_file_data
    nonclass_file_data = context.nonclass_file_data
    ncc = context.ncc
    variable_names = context.variable_names

    for i in range(ncc):
        unique_class: set[str] = set()
        unique_nonclass: set[str] = set()
        for row in class_file_data:
            unique_class.add(row[i])
        for row in nonclass_file_data:
            unique_nonclass.add(row[i])

        class_stripped = set(el.strip() for el in unique_class)
        nonclass_stripped = set(el.strip() for el in unique_nonclass)
        class_diff_ws = unique_class ^ class_stripped
        nonclass_diff_ws = unique_nonclass ^ nonclass_stripped

        if len(class_diff_ws) != 0:
            print_warning_message(context, f"Within the {variable_names[i]} column of the class file, one or more " \
                f"values are distinguished solely by whitespace: {class_diff_ws}. These will be treated as unique values")
        if len(nonclass_diff_ws) != 0:
            print_warning_message(context, f"Within the {variable_names[i]} column of the nonclass file, one or more " \
                f"values are distinguished solely by whitespace: {nonclass_diff_ws}. These will be treated as unique values")

        # Check for values differentiated solely by quotes (single or double)
        class_diff_qu: list[tuple[str,str,str]] = []
        nonclass_diff_qu: list[tuple[str,str,str]] = []
        class_dict = {}
        nonclass_dict = {}
        for el in unique_class:
            nq = el.strip('\'"')
            if nq in class_dict:
                class_diff_qu.append((el, class_dict[nq], nq))
            else:
                class_dict[nq] = el
        for el in unique_nonclass:
            nq = el.strip('\'"')
            if nq in nonclass_dict:
                nonclass_diff_qu.append((el, nonclass_dict[nq], nq))
            else:
                nonclass_dict[nq] = el

        if len(class_diff_qu) != 0:
            print_warning_message(context, f"Within the {variable_names[i]} column of the class file, one or more " \
                f"values are distinguished solely by the presence of quotes: {class_diff_qu}. These will be treated " \
                "as unique values in an occasionally unpredictable manner")
        if len(nonclass_diff_qu) != 0:
            print_warning_message(context, f"Within the {variable_names[i]} column of the nonclass file, one or more " \
                f"values are distinguished solely by the presence of quotes: {nonclass_diff_qu}. These will be treated " \
                "as unique values in an occasionally unpredictable manner")

def detect_possible_continuous(context: CFDContext, cont_threshold=0.3) -> None:

    """
    Detects columns in the DataFrame that may be continuous based on the number of unique values
    relative to the total number of rows.
    * If the number of unique values is less than the threshold, it is likely categorical.
    * If the number of unique values is greater than or equal to the threshold, it is likely continuous.
    \n
    If it is detected as continuous and binning is enabled, the user is given the option to bin the column.
    """

    variable_names = context.variable_names
    class_data = context.class_file_data
    nonclass_data = context.nonclass_file_data
    ncc = context.ncc
    nrc = context.nrc
    nrn = context.nrn
    logs = context.logs
    silent = True if context.silenced or context.silenced_ts else False
    auto_bin = context.auto_bin
    no_bin = context.do_not_bin
    manual_bin = not (auto_bin or no_bin)
    set_num_bins = context.set_bin_num
    set_num = True if set_num_bins != -1 else False
    all_vars = context.bin_all_vars
    by_width = context.bin_by_width

    num_rows = nrc if nrc >= 15 else 0
    num_rows += nrn if nrn >= 15 else 0

    if not set_num and num_rows == 0: # Small data sets can be easily misinterpreted as continuous
        return

    for col in range(ncc):
        un_class_rows = set(tuple(row) for row in class_data)
        un_nonclass_rows = set(tuple(row) for row in nonclass_data)
        cl_vals = [class_data[row][col] for row in range(len(class_data))]
        nc_vals = [nonclass_data[row][col] for row in range(len(nonclass_data))]
        all_vals: list[str] = []
        all_vals.extend(cl_vals)
        all_vals.extend(nc_vals)
        var_name = variable_names[col].strip()
        num_unique = len(set(all_vals))
        # Ignore duplicate rows in comparison
        if all_vars or num_unique / (len(un_class_rows) + len(un_nonclass_rows)) >= cont_threshold:
            if no_bin:
                print_warning_message(context, f"Column '{var_name}' is likely continuous with {num_unique} " \
                    f"unique values among {num_rows} considered instances.\nThe CFD tool does not effectively handle " \
                    "high cardinality variables.\n Consider binning (--bin) or otherwise transforming this column " \
                    "to reduce its cardinality")
                continue
            num_all_vals = []
            try:
                num_all_vals = [float(el) for el in all_vals]
            except:
                try:
                    num_all_vals = [float(el.strip('\'" ')) for el in all_vals]
                    print_warning_message(context, f"Converting the values for feature '{var_name}' to floats was successful " \
                        "only after removing quotes and whitespace. If this was not intended, manually bin and avoid this column")
                except Exception as ex:
                    if not all_vars:
                        print_warning_message(context, f"The '{var_name}' column is likely continuous with {num_unique} " \
                            f"unique values among {num_rows} considered instances. However, it does not contain strictly " \
                            "numerical data, making binning it with the CFD tool impossible. Consider externally binning " \
                            f"or otherwise reducing this column's cardinality manually.\nException: {ex}")
                    else:
                        print_info_message(context, f"Attempting to bin all features failed for feature '{var_name}' " \
                            f"since one or more values could not be converted into a float:\nException: {ex}")
                    continue
            if manual_bin and not all_vars:
                print_info_message(context, f"The '{var_name}' column is a good candidate for binning with {num_unique} " \
                    f"unique numerical values among {num_rows} considered instances", True)
            elif all_vars and not auto_bin:
                print_info_message(context, f"The '{var_name}' column contains {num_unique} unique numerical values " \
                    f"among {num_rows} considered instances", True)

            rec_num_bins = recommended_bins(context, num_all_vals, var_name)
            num_bins = rec_num_bins

            if manual_bin and not set_num:
                print_info_message(context, f"To avoid binning this column, input 0 bins", True)
            while not auto_bin and not set_num:
                num_bins = input(f"How many bins should the '{var_name}' column be divided into? > ")
                try:
                    num_bins = int(num_bins)
                    if num_bins > num_unique or num_bins < 0:
                        print_info_message(context, f"You must chose a number of bins between 1 and the number " \
                            f"of unique values the '{var_name}' column contains ({num_unique}). It is highly recommended " \
                            "to choose a number which reduces the feature's cardinality to a reasonable degree given the " \
                            "number values it holds and the number of instances between your files. To avoid binning it, input 0", True)
                        continue
                except:
                    print_info_message(context, f"Please choose an integer between 1 and {num_unique} as the " \
                        f"number of bins, or 0 to avoid binning '{var_name}'", True)
                    continue
                break

            num_bins = int(num_bins)
            if num_bins >= num_unique or num_bins == 0:
                spec = " since the estimated optimal number of bins equals how many unique values it contains" if all_vars and auto_bin else ""
                print_info_message(context, f"Not performing binning on '{var_name}'{spec}")
                continue

            clusters, _ = kmeans1d.cluster(num_all_vals, num_bins)
            clusters = cast(list[int], clusters)
            if set_num:
                ranges, _ = get_ranges(context.grouping_options[0], context.centroids[0][0], context.centroids[0][1])
            elif by_width:
                ranges, _ = get_ranges(context.grouping_options[num_bins-1], 
                                       context.centroids[num_bins-1][0], context.centroids[num_bins-1][1])
            else:
                ranges, _ = get_ranges(context.grouping_options[num_bins-1], [], 0)

            inf_ranges = [tup for tup in ranges]
            inf_ranges[0] = (-np.inf, inf_ranges[0][1])
            inf_ranges[-1] = (inf_ranges[-1][0], np.inf)
            context.feature_bin_ranges.append((var_name, num_unique, inf_ranges))
            last_cluster = max(clusters)
            def do_replacement(hide_bar: bool, start: float) -> bool:

                """
                Replace the data in context with the binned data for the current feature.
                """

                class_hold: list[list[str]] = [["" * ncc] for _ in range(nrc)]
                nonclass_hold: list[list[str]] = [["" * ncc] for _ in range(nrn)]
                with tq(total=nrc+nrn, desc=f"Binning {var_name}", disable=hide_bar) as pbar:
                    for idx, group in zip([i for i in range(nrc)], clusters[:nrc], strict=True):
                        if start != 0 and time.time() > start + 3:
                            return False
                        pbar.update(1)
                        class_hold[idx] = context.class_file_data[idx]
                        if group == last_cluster:
                            class_hold[idx][col] = f"({inf_ranges[group][0]} - {inf_ranges[group][1]})"
                        else:
                            class_hold[idx][col] = f"({inf_ranges[group][0]} - {inf_ranges[group][1]}]"                            
                    for idx, group in zip([i for i in range(nrn)], clusters[nrc:], strict=True):
                        if start != 0 and time.time() > start + 3:
                            return False
                        pbar.update(1)
                        nonclass_hold[idx] = context.nonclass_file_data[idx]
                        if group == last_cluster:
                            nonclass_hold[idx][col] = f"({inf_ranges[group][0]} - {inf_ranges[group][1]})"
                        else:
                            nonclass_hold[idx][col] = f"({inf_ranges[group][0]} - {inf_ranges[group][1]}]"
                context.class_file_data = class_hold
                context.nonclass_file_data = nonclass_hold
                return True

            if logs and not silent:
                if not do_replacement(True, time.time()):
                    do_replacement(False, 0)
            else:
                do_replacement(True, 0)
            print_info_message(context, f"The '{var_name}' column has been successfully divided into {num_bins} bins. " \
                "The detailed breakdown of ranges is present in info.txt")

def detect_possible_accidental_differentiation_column(context: CFDContext) -> None:

    """
    Detect for the presence of a column meant to separate the data into class and nonclass files, which would
    have all of one value in the class file and all of a different value in the nonclass file.
    This can still be a valid column though, so allow the user the chance to keep it unless auto drop is enabled.
    \n
    Also check for columns which are identical between the class and nonclass files, which will not help in feature differentiation.
    """

    class_file_data = context.class_file_data
    nonclass_file_data = context.nonclass_file_data
    ncc = context.ncc
    variable_names = context.variable_names
    col_drop = context.col_drop

    columns_to_drop: list[int] = []

    for i in range(ncc):
        unique_class: set[str] = set()
        unique_nonclass: set[str] = set()
        for row in class_file_data:
            unique_class.add(row[i])
        for row in nonclass_file_data:
            unique_nonclass.add(row[i])

        if len(unique_class) == 1 and len(unique_nonclass) == 1 and unique_class != unique_nonclass:
            if col_drop == 'auto' or col_drop == '':
                print_info_message(context, f"The {variable_names[i]} column contains only \"{unique_class.pop()}\" in " \
                    f"the class file, and only \"{unique_nonclass.pop()}\" in the nonclass file. This may have been the " \
                    "column used to split the class and nonclass files.\nIf so, it should be removed as its values will " \
                    "not assist with the CFD's calculations.")
            if col_drop == 'all' or col_drop == '':
                drop_me = "" if col_drop == '' else "YES"
                while drop_me.upper() not in ['Y', 'YE', 'YES', 'N', 'NO']:
                    drop_me = input("Would you like to drop this column (Y/N)? >")
                if drop_me.upper() in ['Y', 'YE', 'YES']:
                    columns_to_drop.append(i)

        elif len(unique_class) == 1 and unique_class == unique_nonclass:
            if col_drop == 'auto' or col_drop == 'all':
                columns_to_drop.append(i)
            elif col_drop == '':
                print_info_message(context, f"The {variable_names[i]} column contains only one value for both the " \
                    f"class and nonclass files: \"{unique_class.pop()}\". It should be removed as it will not assist " \
                    "with the CFD tool's calculations", True)
                drop_me = ""
                while drop_me.upper() not in ['Y', 'YE', 'YES', 'N', 'NO']:
                    drop_me = input("Would you like to drop this column (Y/N)? >")
                if drop_me.upper() in ['Y', 'YE', 'YES']:
                    columns_to_drop.append(i)
            else:
                print_warning_message(context, f"The {variable_names[i]} column contains only one value for both the " \
                    f"class and nonclass files: \"{unique_class.pop()}\". It should be removed as it will not assist " \
                    "with the CFD tool's calculations")

    context.column_names_dropped += [variable_names[j] for j in columns_to_drop]

    for idx in sorted(columns_to_drop, reverse=True):
        for row in context.class_file_data:
            del row[idx]
        for row in context.nonclass_file_data:
            del row[idx]
        del context.variable_names[idx]
    context.ncc = len(context.variable_names)

# NOTE: This function is currently not utilized and is a potential future enhancement.
def optimize_column_types(df: pd.DataFrame, category_threshold=0.05) -> pd.DataFrame:

    """
    Optimizes the DataFrame's column types to reduce memory usage and improve performance.
    - Converts boolean-like columns to boolean type.
    - Converts low cardinality columns to category type.
    - Converts fully numeric columns to integer type if possible.
    - Converts object-like columns to string type if they are consistent.
    """

    df_optimized = df.copy()

    for col in df_optimized.columns:
        if pd.api.types.is_bool_dtype(df_optimized[col]) or isinstance(df_optimized[col], pd.CategoricalDtype):
            continue

        col_series = df_optimized[col].apply(lambda x: str(x).strip() if pd.notnull(x) else x)
        unique_vals = col_series.dropna().unique()

        if len(unique_vals) <= 2 and \
        all(str(v).strip().lower() in {"0", "1", "true", "false", "yes", "no"} for v in unique_vals):
            try:
                df_optimized[col] = col_series.astype(bool)
                continue
            except:
                print("Conversion failed")
                pass

        elif len(unique_vals) / len(df_optimized) < category_threshold:
            try:
                df_optimized[col] = col_series.astype("category")
                continue
            except:
                pass

        elif pd.to_numeric(col_series, errors='coerce').notnull().all():
            try:
                df_optimized[col] = pd.to_numeric(col_series, downcast='integer')
                continue
            except:
                pass

        elif pd.api.types.is_object_dtype(df_optimized[col]):
            df_optimized[col] = col_series.astype(str)

    return df_optimized


def expand_bins(bins: list[tuple[float, float]]) -> list[tuple[float, float]]:

    """
    If the ranges do not fully cover all values from -inf to inf,
    expand bins right-ward until they reach their next nearest neighbor
    """

    mod_bins = deepcopy(bins)

    if len(bins) == 1:
        mod_bins = [(-np.inf, np.inf)]
        return mod_bins
    mod_bins[0] = (-np.inf, mod_bins[0][1])
    for i in range(len(bins)-1):
        new_tup = mod_bins[i]
        if mod_bins[i][1] != mod_bins[i+1][0]:
            new_tup = (new_tup[0], mod_bins[i+1][0])
        mod_bins[i] = new_tup
    mod_bins[-1] = (bins[-1][0], np.inf)
    return mod_bins

def get_ranges(lst: list[list[float]], centroids=[], half_width:float=0) -> tuple[list[tuple[float, float]], list[int]]:

        """
        Generate the range of each bin, and how many elements are contained within it.
        """

        ranges: list[tuple[float, float]] = []
        sizes: list[int] = []

        if context.bin_by_width:
            for dx, sub in enumerate(lst):
                ranges.append((centroids[dx]-half_width, centroids[dx]+half_width))
                sizes.append(len(sub))
            ranges = expand_bins(ranges)
            return ranges, sizes

        for sub in lst:
            ranges.append((min(sub), max(sub)))
            sizes.append(len(sub))
        ranges = expand_bins(ranges)
        return ranges, sizes

def recommended_bins(context: CFDContext, data_orig: list[float], feature: str) -> int:

    """
    Bin the data using either a set number or varying number of bins.
    * If manual binning, display choice(s) to the user.
    * If auto binning, select best estimate and don't display.
    * If binning by width, ensure that each bin's width is the same.
    * If binning by frequency, ensure that eah bin's number of elements is the same.
    * If binning by estimate, calculate optional number of bins by examining the overall data shape (currently k-means). This is
    not just using the "elbow method", but rather a weighted combination of several Optimal Bin Contributing Factors (OBCF)s. 
    * The weights were chosen empirically, and are liable for future revision.
    """

    by_width = context.bin_by_width
    by_freq = context.bin_by_freq
    by_estimate = context.bin_by_estimate
    set_num_bins = context.set_bin_num
    set_num = True if set_num_bins != -1 else False
    auto_bin = context.auto_bin
    logs = context.logs
    silent = context.silenced or context.silenced_ts

    if by_width:
        context.centroids.clear()
    display_recs = not auto_bin

    print_timestamp_message(context, f"Calculating the optimal number of bins for {feature}")

    data = deepcopy(data_orig)
    data.sort()
    max_bins = max(int(len(data) / 10), 10)
    max_bins = min(max_bins, len(set(data))) # maximum number of bins the data can be binned with
    inertias: list[float] = [] # stores all inertia values
    all_clusters: list[list[int]] = [] # stores all clusters (which define which bin a given data point belongs to)
    white_spaces: list[float] = [] # stores how much whitespace is present between bins for a given bin grouping

    alt_slopes: list[float] = [] # (current inertia / previous inertia) / (previous inertia / prev-prev inertia)
    inertia_diffs: list[float] = [] # current inertia - previous inertia
    abs_deriv_slopes: list[float] = [] # absolute value of (current inertia - prev inertia) / (prev inertia - prevprev inertia)
    diff_rats: list[float] = [] # current inertia / previous inertia

    # early exit cutoffs so we don't have to calculate up to max_bins under most circumstances
    first_at_alt_exit_co = [max_bins]
    first_at_abs_exit_co = [max_bins]
    first_at_rat_exit_co = [max_bins]

    def early_exit(n: int) -> bool:

        """
        There are 3 early exit flags which can indicate that we should stop calculating early, each based on a different metric.
        - If none are present, do not exit early.
        - If one is present, exit after 20 further calculations if no further flags triggered.
        - If two are present, exit after 15 further calculations from the last.
        - If all three are present, exit 10 further calulations after the last.
        """

        if set_num:
            return False
        if min(first_at_alt_exit_co[0], first_at_abs_exit_co[0], first_at_rat_exit_co[0]) == max_bins:
            return False
        elif min(first_at_alt_exit_co[0], first_at_abs_exit_co[0]) == max_bins:
            return n > first_at_rat_exit_co[0] + 20
        elif min(first_at_alt_exit_co[0], first_at_rat_exit_co[0]) == max_bins:
            return n > first_at_abs_exit_co[0] + 20
        elif min(first_at_abs_exit_co[0], first_at_rat_exit_co[0]) == max_bins:
            return n > first_at_alt_exit_co[0] + 20
        elif max(first_at_alt_exit_co[0], first_at_abs_exit_co[0]) < max_bins:
            return n > max(first_at_alt_exit_co[0], first_at_abs_exit_co[0]) + 15
        elif max(first_at_alt_exit_co[0], first_at_rat_exit_co[0]) < max_bins:
            return n > max(first_at_alt_exit_co[0], first_at_rat_exit_co[0]) + 15
        elif max(first_at_rat_exit_co[0], first_at_abs_exit_co[0]) < max_bins:
            return n > max(first_at_rat_exit_co[0], first_at_abs_exit_co[0]) + 15
        return n > max(first_at_alt_exit_co[0], first_at_abs_exit_co[0], first_at_rat_exit_co[0]) + 10

    def get_inertia(lst: list[list[float]], centers: list[float], n: int) -> bool:

        """
        Calculate the sum of all the squared differences between data points and the center of the bin they fall into.
        Additionally, check whether any early exit flags were met.
        """

        inertia = 0
        for i in range(len(lst)):
            for el in lst[i]:
                inertia += abs(el - centers[i])**2
        if inertia == 0:
            inertias.append(sys.float_info.min) # Avoid a divide by 0 error, while still indicating that we can't do better
            return True
        inertias.append(inertia)

        if set_num:
            return True

        if len(inertias) > 1:
            inertia_diffs.append(inertias[-1] - inertias[-2])

        if len(inertia_diffs) > 1:
            rat_calc = inertia_diffs[-1] / inertia_diffs[-2]
            diff_rats.append(rat_calc) 
            if rat_calc < 0.04 and first_at_rat_exit_co[0] == max_bins: # does the first early exit flag trigger?
                first_at_rat_exit_co[0] = n

        if len(inertias) > 2:
            new_alt_ratio = (inertias[-1]/inertias[-2]) / (inertias[-2]/inertias[-3])
            alt_slopes.append(new_alt_ratio)
            if first_at_alt_exit_co[0] == max_bins and abs(new_alt_ratio) < 1: # does the second?
                first_at_alt_exit_co[0] = n

        if len(inertia_diffs) > 2:
            new_diffs_ratio = abs((inertia_diffs[-1] - inertia_diffs[-2]) / (inertia_diffs[-2] - inertia_diffs[-3]))
            abs_deriv_slopes.append(new_diffs_ratio)
            if first_at_abs_exit_co[0] == max_bins and abs(new_diffs_ratio) < 0.09: # does the third?
                first_at_abs_exit_co[0] = n
        return False

    centroids: list[float] = []
    grouping_options: list[list[list[float]]] = []
    ez_exit_bin = -1

    def width_lists(data: list[float], n: int) -> tuple[list[int], list[float]]:

        """
        Divide the data into n equal width bins
        """

        bin_width = round((max(data)-min(data)) / n, 6)
        half_width = round(bin_width / 2, 6)
        cur_st = min(data) - bin_width
        clusters: list[int] = []
        centroids: list[float] = []
        for _ in range(n):
            cur_st += bin_width
            centroids.append(round(cur_st + half_width, 6))
        for el in data:
            success = False
            for idx, bin_center in enumerate(centroids[:-1]):
                if el >= bin_center - half_width and el < bin_center + half_width:
                    clusters.append(idx)
                    success = True
                    break
            if not success:
                clusters.append(len(centroids)-1)
        context.centroids.append((centroids, half_width))
        return clusters, centroids

    check_for_freq_exit = True

    def freq_lists(data: list[float], n: int) -> tuple[list[int], list[float]]:

        """
        Divide the data into n bins of equal frequency (amount of data in each).
        Data cannot appear in more than one bin, leading to approximate equality of frequency
        """

        nonlocal check_for_freq_exit
        clusters: list[int] = []
        centroids: list[float] = []

        # First attempt (use pandas to split the bins):
        try:
            pdata = {'value': data}
            df = pd.DataFrame(pdata)
            df['frequency_bin'] = pd.qcut(df['value'], q=n)
            pdbins = pd.qcut(df['value'], q=n, retbins=True)
            cur_bin = pdbins[0][0]
            cur_group = []
            b = 1
            for dat, bin in zip(data, pdbins[0], strict=True):
                if bin == cur_bin:
                    cur_group.append(dat)
                    clusters.append(b-1)
                    continue
                cur_bin = bin
                centroids.append(sum(cur_group)/len(cur_group))
                cur_group = [dat]
                clusters.append(b)
                b += 1
            centroids.append(sum(cur_group)/len(cur_group))
            assert(len(data) == len(clusters))
            return clusters, centroids
        except ValueError:
            # Pandas binning can refuse to bin with certain numbers of bins when it thinks it knows better
            # When this happens, fall back to this manual implementation (slower, so avoid if able)
            uniq_data = sorted(list(set(data)))
            opt_per_bin = len(data) / n # optimal number of entries per bin
            counts: dict[float, int] = {dat: data.count(dat) for dat in uniq_data}
            k = len(uniq_data)
            count = 0
            for p in range(1, k+1):
                for b in range(1, min(n+1,p+1)):
                    if b == 1:
                        count += 1
                        continue
                    for _ in range(1, p):
                        count += 1
            total_iters = count

            all_potential_splits_through_point: dict[int, dict[int, list[list[list[float]]]]] = {}
                                    # pos in uniq: {num_bins to pos: binning arrangement}
            opt_splits_through_point: dict[int, dict[int, list[list[float]]]] = {}
                        # same as above but each x.y only has the best list for that config

            def evaluate_split(split: list[list[float]]) -> float:

                """
                Evaluate a split by the sum of the square difference between the bin sizes and the optimal bin size.
                """

                diff_sum = 0
                for bin in split:
                    bin_sum = sum([counts[el] for el in bin])
                    diff_sum += abs(bin_sum - opt_per_bin)**2
                return diff_sum

            def manual_find_splits(pbar: tq, start: float=0) -> bool:

                nonlocal all_potential_splits_through_point
                nonlocal opt_splits_through_point

                all_potential_splits_through_point.clear()
                opt_splits_through_point.clear()
                for pos in range(1, len(uniq_data) + 1):
                    if start != 0 and time.time() - start > 3:
                        return False
                    all_potential_splits_through_point[pos] = {}
                    opt_splits_through_point[pos] = {}
                    for num_bins in range(1, min(n + 1, pos+1)):
                        all_potential_splits_through_point[pos][num_bins] = []
                        if num_bins == 1:
                            all_potential_splits_through_point[pos][num_bins].append([uniq_data[:pos]])
                            opt_splits_through_point[pos][num_bins] = [uniq_data[:pos]]
                            pbar.update(1)
                            continue

                        # Build splits by adding the current element to existing splits
                        for split_pos in range(1, pos):
                            num_bins_prev = num_bins - 1
                            if num_bins_prev not in opt_splits_through_point[split_pos]:
                                pbar.update(1)
                                continue
                            prev_split = opt_splits_through_point[split_pos][num_bins_prev]
                            new_split = deepcopy(prev_split)
                            new_split.append(uniq_data[split_pos:pos])
                            all_potential_splits_through_point[pos][num_bins].append(new_split)
                            pbar.update(1)

                        #Evaluate the splits and keep only the optimal one
                        best_split: list[list[float]] = []
                        best_eval = float('inf')
                        for split in all_potential_splits_through_point[pos][num_bins]:
                            eval = evaluate_split(split)
                            if eval < best_eval:
                                best_eval = eval
                                best_split = split
                        opt_splits_through_point[pos][num_bins] = best_split
                return True

            pbar_off = tq(total=total_iters, desc=f"Frequency for {n} Bins", disable=True)
            if logs and not silent:
                res = manual_find_splits(pbar_off, time.time())
                pbar_off.close()
                if not res:
                    pbar_on = tq(total=total_iters, desc=f"Frequency for {n} Bins")
                    manual_find_splits(pbar_on)
                    pbar_on.close()
            else:
                manual_find_splits(pbar_off)
            pbar_off.close()

            clusters: list[int] = []
            centroids: list[float] = []
            cur_group = []
            cur_cluster_pos = 0
            cur_cluster: list[float] = opt_splits_through_point[len(uniq_data)][n][0]
            # The very best configuration will be the final bin's best way to bin n bins through and including itself
            for dat in data:
                if dat in cur_cluster:
                    clusters.append(cur_cluster_pos)
                    cur_group.append(dat)
                else:
                    centroids.append(sum(cur_group)/len(cur_group))
                    cur_group = [dat]
                    cur_cluster_pos += 1
                    cur_cluster = opt_splits_through_point[len(uniq_data)][n][cur_cluster_pos]
                    clusters.append(cur_cluster_pos)
            centroids.append(sum(cur_group)/len(cur_group))

        try:
            assert(len(data) == len(clusters))
        except AssertionError:
            print_warning_message(context, f"Binning by Frequency for {n} bins failed, however data will still be displayed")
        return clusters, centroids

    for n in range(1, max_bins+1):
        if early_exit(n):
            break
        if set_num:
            n = set_num_bins
        final_groupings: dict[int, list[float]] = {}
        groupings_lst: list[list[float]] = []
        if by_estimate:
            clusters, centroids = kmeans1d.cluster(data, n)
            clusters = cast(list[int], clusters)
            centroids = cast(list[float], centroids)
        elif by_width:
            clusters, centroids = width_lists(data, n)
        elif by_freq:
            clusters, centroids = freq_lists(data, n)
        else:
            print_warning_message(context, "Should never occur -- unsure how to bin data", True)
            clusters, centroids = [], []
        all_clusters.append(clusters)

        for i in range(max(clusters)+1):
            final_groupings[i] = []
        for elem, pos in zip(data, clusters):
            final_groupings[pos].append(elem)
        for i in range(max(clusters)+1):
            groupings_lst.append(final_groupings[i])
        grouping_options.append(groupings_lst)
        easy_exit = get_inertia(groupings_lst, centroids, n)

        if easy_exit:
            ez_exit_bin = n
            break

        def get_whitespace(group_lst: list[list[float]]) -> float:

            """
            Calculate how much empty space is between the bins with this many bins.
            """

            whitespace = 0
            cur_st = max(group_lst[0])
            if len(group_lst) <= 1:
                return 0
            for sub in group_lst[1:]:
                if not sub:
                    continue
                whitespace += min(sub) - cur_st
                cur_st = max(sub)
            return whitespace
        white_spaces.append(get_whitespace(groupings_lst))

    context.grouping_options = grouping_options

    if not set_num:
        # 2 OBCFs
        cl_to_zero = [-1, 999]
        cl_to_zero_alt = [-1, 999] # find the element closest to 0 within each range.

        for i in range(len(abs_deriv_slopes)):
            if abs_deriv_slopes[i] < cl_to_zero[1]:
                cl_to_zero = [i+2, abs_deriv_slopes[i]]
            if abs(alt_slopes[i]) < cl_to_zero_alt[1]:
                cl_to_zero_alt = [i+2, abs(alt_slopes[i])]

        normal_inertias = [10 * el / max(inertias) for el in inertias]
        n_inertia_slopes = [normal_inertias[i] - normal_inertias[i+1] for i in range(len(normal_inertias)-1)]
        n_inertia_rats = [normal_inertias[i] / normal_inertias[i+1] for i in range(len(normal_inertias)-1)]
        n_inertia_slope_rats = [n_inertia_slopes[i] / n_inertia_slopes[i+1] for i in range(len(n_inertia_slopes)-1)]

        # 4 more OBCFs
        first_normal_before_co = [-1, 999]
        normal_slope = [-5, 0]
        normal_rat = [-5, 0]
        normal_slope_rat = [-5, 0]

        # Empirically chosen
        normal_co = 1.2
        Slope_Cutoff = 0.5
        Ratio_Cutoff = 1.3
        Slope_Ratio_Cutoff = 1.3

        for i in range(len(normal_inertias)-1):
            if normal_inertias[i+1] < normal_co:
                first_normal_before_co = [i+2, normal_inertias[i]]
                break

        for q, slope in enumerate(n_inertia_slopes):
            if slope < Slope_Cutoff:
                normal_slope = [q+1, slope]
                break

        for q, rat in enumerate(n_inertia_rats):
            if rat < Ratio_Cutoff:
                normal_rat = [q+1, rat]
                break

        max_pos_rat = n_inertia_rats.index(max(n_inertia_rats))
        after_last_max_rat = [max_pos_rat + 2, n_inertia_rats[max_pos_rat]] # OBCF

        for q, rat in enumerate(n_inertia_slope_rats):
            if rat < Slope_Ratio_Cutoff:
                normal_slope_rat = [q+1, rat]
                break

        max_pos = n_inertia_slope_rats.index(max(n_inertia_slope_rats))
        after_last_max_slope_rat = [max_pos + 2, n_inertia_slope_rats[max_pos]] # OBCF
        diff_rats_idx = diff_rats.index(min(diff_rats)) + 2 # OBCF

        whitespace_diffs: list[float] = np.diff(white_spaces).tolist()
        whitespace_diffs.remove(max(whitespace_diffs))
        mean_ws = np.mean(whitespace_diffs)
        mean_ws *= 3.5 # Empirically chosen
        dip_co = np.mean([abs(el) for el in whitespace_diffs])
        dip_co *= 0.5 # Empirically chosen
        can_jump_high = False

        # 5 OBCFs
        last_jump = [0, 0]
        first_dip = [0, 0]
        final_dip = [0, 0]
        biggest_jump_after_first = [0, 0]
        first_big_jump = [0, 0]

        for i in range(len(white_spaces)-1):
            if white_spaces[i+1] - white_spaces[i] > mean_ws:
                if not can_jump_high and i > 2:
                    first_big_jump = [i+2, white_spaces[i+1] - white_spaces[i]]
                if can_jump_high and white_spaces[i+1] - white_spaces[i] > biggest_jump_after_first[1]:
                    biggest_jump_after_first = [i+2, white_spaces[i+1] - white_spaces[i]]
                can_jump_high = True
                last_jump = [i+2, white_spaces[i+1] - white_spaces[i]]
            if first_dip[0] == 0 and white_spaces[i+1] < white_spaces[i]:
                first_dip = [i+1, white_spaces[i] - white_spaces[i+1]]
            if white_spaces[i] - white_spaces[i+1] >= dip_co:
                final_dip = [i+1, white_spaces[i] - white_spaces[i+1]]

        bin_choices = Counter()

        # All weights were empirically chosen. 
        # 2 bins is typically over-preferred, and as such its weights are specifically reduced.
        if ez_exit_bin != -1:
            bin_choices.update({str(ez_exit_bin): 1000})
        if after_last_max_slope_rat[0] > 2:
            bin_choices.update({str(after_last_max_slope_rat[0]): 2.5})
        else:
            bin_choices.update({str(after_last_max_slope_rat[0]): 0.7})
        if after_last_max_rat[0] > 2:
            bin_choices.update({str(after_last_max_rat[0]): 1.4})
        else:
            bin_choices.update({str(after_last_max_rat[0]): 0.4})
        bin_choices.update({str(last_jump[0]): 1.3})
        bin_choices.update({str(normal_rat[0]): 1.1})
        if diff_rats_idx != 2:
            bin_choices.update({str(diff_rats_idx): 1})
        else:
            bin_choices.update({str(diff_rats_idx): 0.5})
        bin_choices.update({str(normal_slope[0]): 1.2})
        bin_choices.update({str(first_big_jump[0]): 1})
        if last_jump[0] == biggest_jump_after_first[0]:
            bin_choices.update({str(biggest_jump_after_first[0]): 0.7})
        else:
            bin_choices.update({str(biggest_jump_after_first[0]): 0.3})
        bin_choices.update({str(first_normal_before_co[0]): 1})
        if first_dip[1] > 4:
            bin_choices.update({str(first_dip[0]): 1})
        else:
            bin_choices.update({str(first_dip[0]): 0.5})
        if first_dip[0] != final_dip[0]:
            bin_choices.update({str(final_dip[0]): 1})
        bin_choices.update({str(cl_to_zero_alt[0]): 0.9})
        bin_choices.update({str(cl_to_zero[0]): 0.8})
        bin_choices.update({str(normal_slope_rat[0]): 0.8})

        to_remove: list[str] = []
        for key in bin_choices:
            # Don't bin with just one bin, and ignore any OBFC's which did not trigger
            if int(key) <= 1:
                to_remove.append(key)
        for key in to_remove:
            del bin_choices[key]

        best_bins_strs: list[tuple[str,int]] = bin_choices.most_common()

        if len(best_bins_strs) > 1:
            i = 0
            while i < len(best_bins_strs) - 1:
                if best_bins_strs[i][0] == '2' and best_bins_strs[i+1][1] >= best_bins_strs[i][1] - 1:
                    hold = best_bins_strs[i]
                    best_bins_strs[i] = best_bins_strs[i+1]
                    best_bins_strs[i+1] = hold
                i += 1
            # Exactly 2 bins is still over preferred, despite initial priority downgrading
            # So, if the next best option(s) are almost as good or equal, prefer them instead

        if len(best_bins_strs) > 3: # get the best 3 binning choices
            best_bins_strs = best_bins_strs[:3]

        best_bins = [int(el) for el, _ in best_bins_strs]

        if best_bins_strs[-1][1] * 8 < best_bins_strs[0][1]: # if the weight of the third place choice is too low, remove it.
            best_bins.pop()
    else: # if set_num
        best_bins = [set_num_bins]

    if display_recs:
        # Make the 2x2 plot
        fig, axes = plt.subplots(2, 2, figsize=(10, 10), layout='constrained')
        ax1 = cast(mpl_axes.Axes, axes[0, 0])
        ax2 = cast(mpl_axes.Axes, axes[0, 1])
        ax3 = cast(mpl_axes.Axes, axes[1, 0])
        ax4 = cast(mpl_axes.Axes, axes[1, 1])

        single_choice = False
        if len(best_bins) < 3:
            ax4.set_axis_off()
            if len(best_bins) < 2:
                single_choice = True
        class interactive_line_plot:
            def __init__(self, ax: mpl_axes.Axes):
                self.ax = ax
                self.cid = ax.figure.canvas.mpl_connect('button_press_event', self) # type: ignore

            def __call__(self, event: Event):
                if set_num:
                    return
                if event.inaxes == self.ax:

                    if event.xdata is not None:
                        x = int(round(event.xdata))
                        if x <= 0:
                            return
                    else:
                        return
                    mod_ax = ax3 if single_choice else ax4
                    try:
                        mod_ax.clear()
                        make_plot(mod_ax, x, True)
                        fig.canvas.draw()
                    except Exception:
                        pass

        interactive_line_plot(ax1)

        ax1.set_title(f"Inertia vs. Number of Bins for {feature}")
        ax1.set_xlim(0, len(inertias) + 1)
        ax1.set_xticks([2 * el for el in range(0, int((len(inertias)+4) / 2))])
        ax1.plot(range(1, len(inertias)+1), inertias, marker='o', color='blue', linestyle='-')
        ax1.set_xlabel('Number of Bins -- Click Points to Display')
        ax1.set_ylabel('Inertia')

        if set_num:
            ax3.set_axis_off()
            ax4.set_axis_off()
            ax1.clear()
            ax1.set_axis_off()
        else:
            line_colors = ["#00FF00", "#FFD000", "#FF0000"]
            for idx, el in enumerate(best_bins):
                ax1.axvline(el, color=line_colors[idx])
            ax1.grid(True)

        def make_plot(ax: mpl_axes.Axes, num: int, manual=False):
            centr = []
            half_width = 0
            if by_width and set_num:
                centr = context.centroids[0][0]
                half_width = context.centroids[0][1]
            elif by_width:
                best_bin = best_bins[num-2] if not manual else num
                centr = context.centroids[best_bin-1][0]
                half_width = context.centroids[best_bin-1][1]
            if set_num:
                best_bin = set_num_bins
                range_size = get_ranges(grouping_options[0], centr, half_width)
            else:
                best_bin = best_bins[num-2] if not manual else num
                range_size = get_ranges(grouping_options[best_bin-1], centr, half_width)
            ranges = range_size[0]
            sizes = range_size[1]
            sum_s = sum(sizes)
            sizes_decimals = [el / sum_s for el in sizes]

            if by_width:
                ax.set_title(f"{feature} Binned with {best_bin} Equal Width Bins")
            elif by_freq:
                ax.set_title(f"{feature} Binned with {best_bin} Equal Freq Bins")
            else:
                ax.set_title(f"{feature} Binned with {best_bin} K-Means Bins")
            ax.set_xlabel("Data")
            ax.set_ylabel("Data % Per Bin")

            if sizes and any(sizes):
                y_mn_lbl = min(sizes_decimals)/3
                y_mx_lbl = max(sizes_decimals)
            else:
                y_mn_lbl = 0
                y_mx_lbl = 1
            y_tix = []
            y_tix += [round(y_mn_lbl + i * (y_mx_lbl - y_mn_lbl) / 4, 3) for i in range(5)]
            ax.set_yticks(y_tix)
            colors = ['red', 'orange', 'yellow', 'green', 'blue', 'purple']
            mx_dat = max(data)
            mn_dat = min(data)
            min_bin_width = (mx_dat-mn_dat)/40
            ranges_nudged = deepcopy(ranges)
            i = 0
            while i < len(ranges_nudged):
                start = ranges_nudged[i][0]
                end = ranges_nudged[i][1]
                if start == -np.inf:
                    start = mn_dat
                if end == np.inf:
                    end = mx_dat
                if i > 0 and start < ranges_nudged[i-1][1]:
                    start = ranges_nudged[i-1][1]
                if end - start < min_bin_width:
                    if i == 0 or ranges_nudged[i-1][1] <= start - (min_bin_width - (end - start))/2:
                        end += (min_bin_width - (end - start))/2
                        start -= (min_bin_width - (end - start))/2
                    else:
                        end += (min_bin_width - (end - start))
                ranges_nudged[i] = (start, end)
                i += 1
            ax.margins(x=0)
            dat_rng = mx_dat - mn_dat
            edge_ext = dat_rng * 0.1
            ax.set_xlim(mn_dat - edge_ext, mx_dat + edge_ext)
            for i, (start, end), height in zip(range(len(ranges_nudged)), ranges_nudged, sizes_decimals):
                width_val = end - start
                alp = 0.7 if width_val == min_bin_width else 0.5
                ax.bar(x=[(start + end) / 2], height=[height], width=[width_val], color='black', alpha=1)
                ax.bar(x=[(start + end) / 2], height=[y_mx_lbl * 1.2], width=[width_val], color=colors[i % len(colors)], alpha=alp)
                if ranges[i][0] == -np.inf:
                    ax.axvspan(mn_dat - edge_ext, start, color=colors[i % len(colors)], alpha=0.2)
                if ranges[i][1] == np.inf:
                    ax.axvspan(end, mx_dat + edge_ext, color=colors[i % len(colors)], alpha=0.2)
            if max(y_tix) == 0:
                y_mx_lbl = 1
            ax.set_ylim(min(y_tix), y_mx_lbl * 1.2)
            ax.scatter(data, [y_mx_lbl * 1.1 for _ in range(len(data))], color='black', alpha=0.1)
            x_labels = [f"({round(start, 2)} - {round(end, 2)}]" for start, end in ranges]
            x_labels[-1] = x_labels[-1][:-1] + ')' # positive infinity is an open bracket
            accept = False
            for idx, tup in enumerate(ranges_nudged):
                if idx > 0 and tup[1]-tup[0] == min_bin_width and not accept and idx != len(ranges_nudged)-1:
                    x_labels[idx] = ''
                    accept = True
                else:
                    accept = False
            label_rotate = 45 + min(3 * len(ranges), 45)
            ax.set_xticks([start+(end-start)/2 for start, end in ranges_nudged], x_labels)
            ax.tick_params('x', labelrotation=label_rotate, labelsize='small', length=10, pad=0.1)
            if label_rotate < 84:
                ax.set_xticklabels(ax.get_xticklabels(), ha='right', rotation_mode='anchor')

        make_plot(ax2, 2)
        if len(best_bins) >= 2:
            make_plot(ax3, 3)
        if len(best_bins) == 3:
            make_plot(ax4, 4)
        plt.show()

    return best_bins[0]

def get_set_files(context: CFDContext) -> None:

    """
    Loads the class and nonclass files into the context, optionally removing duplicates and incomplete rows.
    It also detects if the files have headers and sets the variable names accordingly.
    """

    class_file_path = context.class_file_path
    nonclass_file_path = context.nonclass_file_path
    verbose = context.verbose
    overwrite = context.overwrite
    delimiter = context.delimiter
    output = context.output_path
    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff

    sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    variable_names = []

    if os.path.exists(sub_dir_name):
        if not overwrite:
            print_warning_message(context, f"The output folder {sub_dir_name} already exists. " \
                "If you want to always overwrite it, please use the -o/--overwrite flag")
            response = input("Do you want to remove the old folder and continue? (Y/N): ")
            if response.upper() != "Y" and response.upper() != "YES":
                sys.exit(0)
        shutil.rmtree(sub_dir_name, ignore_errors=True) # sub_dir_name sanitized by this step, should be safe

    print_timestamp_message(context, "Begin class file loading")

    # Class File

    eng = 'c'
    sample = ''
    if len(delimiter) > 1:
        eng = 'python'
    try:
        with open(class_file_path, 'r') as f:
            sample = f.read(2048)
            f.close()
    except Exception as ex:
        if context.force:
            print_warning_message(context, f"Force has bypassed {ex}")
        else:
            print_warning_message(context, f"The expected class file was not found at '{class_file_path}'.\n" \
                f"Error Message: \"{str(ex).strip()}\"", True)

    sniffer = csv.Sniffer()
    dialect = sniffer.sniff(',')
    try:
        dialect = sniffer.sniff(sample, delimiters=",;| \t")
    except Exception as ex:
        if context.force:
            print_warning_message(context, f"Force has bypassed {ex}")
        else:
            print_warning_message(context, f"Something went wrong when trying to determine the " \
                f"delimiter for '{class_file_name}'.\nPlease ensure that it is properly formatted and not empty.\n" \
                f"Error Message: \"{str(ex).strip()}\"", True)

    if not context.force and delimiter is not dialect.delimiter:
        print_warning_message(context, f"The expected delimiter '{delimiter}' was not found in '{class_file_name}'.\n" \
            f"Instead, the '{dialect.delimiter}' character was deduced to be the delimiting character.\nPlease ensure " \
            "that your CSVs either use a comma as their delimiter, or that you specify one using the delimiter flag.\n" \
            "For tabs or spaces, use \"-d '\\s+'\"", True)
    class_df = None
    try:
        class_df = pd.read_csv(class_file_path, sep=delimiter, header=None, dtype=str, engine=eng)
        no_nan_class_df = class_df.fillna('__NAN__')
        if not class_df.equals(no_nan_class_df):
            print_warning_message(context, "One or more NaN or equivalent values in the class file have been converted " \
                "to __NAN__")
            class_df = no_nan_class_df
    except Exception as ex:
        if context.force:
            print_warning_message(context, f"Force has bypassed {ex}")
        else:
            print_warning_message(context, f"Something went wrong when trying to read '{class_file_name}' as a CSV.\n" \
                f"Please ensure that it is properly formatted and not empty.\nError message: \"{str(ex).strip()}\"", True)
    class_df = cast(pd.DataFrame, class_df)

    if class_df.empty:
        print_warning_message(context, f"The class file '{class_file_name}' is empty after removing incomplete rows", True)

    if detect_header(class_df):
        context.has_header = True
        context.variable_names = variable_names = class_df.iloc[0].tolist()
        lengths = [len(str(name)) for name in variable_names]
        context.max_name_length = max(lengths)
        context.class_file_data = class_df.iloc[1:].values.tolist()
    else:
        context.class_file_data = class_df.values.tolist()

    class_file_data = context.class_file_data

    if not class_file_data:
        print_warning_message(context, f"The class file, '{class_file_name}', is empty after header detection.\n" \
            "Please ensure that the file contains data beyond a header", True)

    context.nrc = len(class_file_data)
    context.ncc = ncc = len(class_file_data[0])

    # Nonclass File

    print_timestamp_message(context, "Begin nonclass file loading")
    eng = 'c'
    if len(delimiter) > 1:
        eng = 'python'
    try:
        with open(nonclass_file_path, 'r') as f:
            sample = f.read(2048)
            f.close()
    except Exception as ex:
        if context.force:
            print_warning_message(context, f"Force has bypassed {ex}")
        else:
            print_warning_message(context, f"The expected nonclass file was not found at '{nonclass_file_path}'.\n" \
                f"Error Message: \"{str(ex).strip()}\"", True)

    sniffer = csv.Sniffer()
    dialect = sniffer.sniff(",")
    try:
        dialect = sniffer.sniff(sample, delimiters=",;| \t")
    except Exception as ex:
        if context.force:
            print_warning_message(context, f"Force has bypassed {ex}")
        else:
            print_warning_message(context, f"Something went wrong when trying to determine the delimiter for " \
                f"'{nonclass_file_name}'.\nPlease ensure that it is properly formatted and not empty.\n" \
                f"Error Message: \"{str(ex).strip()}\"", True)

    if not context.force and delimiter is not dialect.delimiter:
        print_warning_message(context, f"The expected delimiter '{delimiter}' was not found in '{nonclass_file_name}'.\n" \
            f"Instead, the '{dialect.delimiter}' character was deduced to be the delimiting character.\n Please ensure " \
            "that your CSVs either use a comma as their delimiter, or that you specify one using the delimiter flag.\n" \
            "For tabs or spaces, use \"-d '\\s+'\"", True)
    nonclass_df = None
    try:
        nonclass_df = pd.read_csv(nonclass_file_path, sep=delimiter, header=None, dtype=str, engine=eng)
        no_nan_nonclass_df = nonclass_df.fillna('__NAN__')
        if not nonclass_df.equals(no_nan_nonclass_df):
            print_warning_message(context, "One or more NaN or equivalent values in the nonclass file have been " \
                "converted to __NAN__")
            nonclass_df = no_nan_nonclass_df
    except Exception as ex:
        if context.force:
            print_warning_message(context, f"Force has bypassed {ex}")
        else:
            print_warning_message(context, f"Something went wrong when trying to read '{nonclass_file_name}' as a CSV.\n" \
                f"Please ensure that it is properly formatted and not empty.\nError message: \"{str(ex).strip()}\"", True)

    nonclass_df = cast(pd.DataFrame, nonclass_df)

    if nonclass_df.empty:
        print_warning_message(context, f"The nonclass file '{nonclass_file_name}' is empty after removing incomplete rows", True)

    if detect_header(nonclass_df):

        variable_names_nonclass = nonclass_df.iloc[0].tolist()

        if context.has_header and (len(context.variable_names) != len(variable_names_nonclass)):
            print_warning_message(context, f"Both files must refer to the same number of variables.\n" \
                f"'{context.class_file_name}' refers to {len(context.variable_names)} variables, while " \
                f"'{context.nonclass_file_name}' refers to {len(variable_names_nonclass)} variables", True)
        elif context.has_header and (context.variable_names != variable_names_nonclass):
            print_warning_message(context, f"Both files must refer to the same variables:\n" \
                f"'{context.class_file_name}' refers to: {variable_names}, while\n" \
                f"'{context.nonclass_file_name}' refers to: {variable_names_nonclass}", True)

        context.has_header = True
        context.nonclass_file_data = nonclass_df.iloc[1:].values.tolist()
    else:
        context.nonclass_file_data = nonclass_df.values.tolist()

    nonclass_file_data = context.nonclass_file_data

    if not nonclass_file_data:
        print_warning_message(context, f"The nonclass file, '{nonclass_file_name}', is empty after header detection.\n" \
            "Please ensure that the file contains data beyond a header", True)

    context.nrn = len(nonclass_file_data)
    ncn = len(nonclass_file_data[0])

    # Misc Error Check

    if ncn != ncc:
        print_warning_message(context, f"Both files must refer to the same variables.\n" \
            f"'{context.class_file_name}' contains {ncc} columns while '{context.nonclass_file_name}' contains {ncn}", True)

    if variable_names and not verbose:
        print_warning_message(context, "A header was detected AND REMOVED FROM DATA in one or both files, " \
            "but verbose (-v) mode was not enabled")

    if not variable_names or not verbose:
        context.variable_names = []
        if verbose:
            print_warning_message(context, "Verbose mode was enabled but NO VARIABLE NAMES were detected. " \
                "Using default variable names")
        for i in range(ncc):
            context.variable_names.append(f"Var {i}")

    # Check for multiple variables with the same name
    seen: set[str] = set()
    duplicates: list[str] = []
    for name in context.variable_names:
        if name in seen:
            duplicates.append(name)
        else:
            seen.add(name)
    if duplicates:
        plural = "variables have" if len(duplicates) != 1 else "variable has"
        print_warning_message(context, f"The following {plural} multiple instances with the same name:\n" \
            f"{[f'{name}' for name in duplicates]}\nPlease ensure all variables have unique names", True)

    class_set = {str([val for val in inner_list]) for inner_list in class_file_data}
    nonclass_set = {str([val for val in inner_list]) for inner_list in nonclass_file_data}

    if class_set == nonclass_set:
        print_warning_message(context, "Class and nonclass files are identical. Please provide different files", True)
    elif class_set.issubset(nonclass_set):
        print_warning_message(context, f"'{context.class_file_name}' is a subset of '{context.nonclass_file_name}'.\n" \
            "Please ensure that the class file contains unique data that is not present in the nonclass file", True)
    elif nonclass_set.issubset(class_set):
        print_warning_message(context, f"'{context.nonclass_file_name}' is a subset of '{context.class_file_name}'.\n" \
            "Please ensure that the nonclass file contains unique data that is not present in the class file", True)

    print_timestamp_message(context, "Detecting potentially continuous features")
    detect_possible_continuous(context)
    print_timestamp_message(context, "Detecting duplciate rows")
    remove_duplicate_rows(context)
    print_timestamp_message(context, "Checking for potentially erronous columns")
    detect_possible_accidental_differentiation_column(context)
    print_timestamp_message(context, "Checking for potentially erronous feature names")
    detect_possible_unintentionally_unique_variable_names(context)

    num_cols_dropped = len(context.column_names_dropped)
    if num_cols_dropped > 0:
        plural = ("columns were", "They are") if num_cols_dropped > 1 else ("column was", "It is")
        print_info_message(context, f"{num_cols_dropped} {plural[0]} dropped from the data. {plural[1]} logged in info.txt")
    elif context.col_drop != 'NONE':
        print_info_message(context, "No columns were dropped")

    # Sanitize Variable Names
    san_names = [sanitize_name(var_name) if isinstance(var_name, str) else var_name for var_name in context.variable_names]
    old_names = [item for item in context.variable_names if item not in san_names]

    size_diff = len(context.variable_names) - len(set(san_names))
    if size_diff != 0:
        plural = "features" if size_diff != 1 else "feature"
        print_warning_message(context, f"Sanitizing variable names resulted in {size_diff} {plural} " \
            "with the same name.\nPlease ensure that your variable names are not differentiated by characters " \
            "which must be escaped (ex, quotes (\", \'), slashes (\\, /), semicolons, ampersands, etc.)", True)

    if old_names:
        new_names = [item for item in san_names if item not in context.variable_names]
        plural = "names have" if len(old_names) != 1 else "name has"
        print_info_message(context, f"{len(old_names)} variable {plural} been santized to prevent unpredictable parsing")
        for i in range(len(old_names)):
            print_info_message(context, f"{old_names[i]} ==> {new_names[i]}")

    context.variable_names = san_names
    context.class_row_DVC_occurrence_counts = {i: [] for i in range(context.nrc)}
    context.nonclass_row_DVC_occurrence_counts = {i: [] for i in range(context.nrn)}
    sanitize_values(context)

    print_timestamp_message(context, "Files loaded")

class CombinationCounter:
    def __init__(self, file_data: list[list[str]], file_name: str):
        self.data: list[list[str]] = file_data
        self.file = file_name
        # Dictionary where values map to how often they appear in the file
        self.one_way_counts: dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency] = defaultdict(int)
        self.two_way_counts: dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency] = defaultdict(int)
        self.three_way_counts: dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency] = defaultdict(int)
        self.four_way_counts: dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency] = defaultdict(int)
        self.five_way_counts: dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency] = defaultdict(int)
        self.six_way_counts: dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency] = defaultdict(int)
        self.distinct_values: dict[ValueIndex, set[ValueString]] = defaultdict(set)

    def count_combinations(self, context: CFDContext) -> None:

        logs = context.logs
        max_ways = context.max_t_ways
        silent = context.silenced or context.silenced_ts

        def perform_calcs(hide_bar: bool, timeout: bool) -> bool:

            start_time = time.time()
            illegal_values: set[str] = set()
            for row in tq(self.data, desc=f'{self.file} Calculations', disable=hide_bar):
                if timeout and time.time() - start_time > 3:
                    return False
                indexed_values: list[ValueCombo_Tuple_index_str] = \
                    [(index, value) for index, value in enumerate(row) if pd.notnull(value)]

                for idx, value in enumerate(indexed_values):
                    i, val = value
                    if ';' in val:
                        if not context.force:
                            print_warning_message(context, f"One or more values, at a minimum {val}, contains a semicolon. " \
                                "Semicolons are used as delimiters in the DVC csv outputs, as commas appear more frequently " \
                                "in values. Please ensure no values contain a semicolon in your class or nonclass files", True)
                        else:
                            indexed_values[idx] = (i, val.replace(';', '_'))
                            if val not in illegal_values:
                                illegal_values.add(val)
                                print_warning_message(context, f"Force has bypassed an illegal semicolon in the value " \
                                    f"{val}. It has been replaced with an underscore")
                for combo in combinations(indexed_values, 1):
                    self.one_way_counts[combo] += 1
                if max_ways >= 2:
                    for combo in combinations(indexed_values, 2):
                        self.two_way_counts[combo] += 1
                if max_ways >= 3:
                    for combo in combinations(indexed_values, 3):
                        self.three_way_counts[combo] += 1
                if max_ways >= 4:
                    for combo in combinations(indexed_values, 4):
                        self.four_way_counts[combo] += 1
                if max_ways >= 5:
                    for combo in combinations(indexed_values, 5):
                        self.five_way_counts[combo] += 1
                if max_ways == 6:
                    for combo in combinations(indexed_values, 6):
                        self.six_way_counts[combo] += 1
            return True

        if logs and not silent:
            if not perform_calcs(True, True):
                self.one_way_counts.clear()
                self.two_way_counts.clear()
                self.three_way_counts.clear()
                self.four_way_counts.clear()
                self.five_way_counts.clear()
                self.six_way_counts.clear()
                perform_calcs(False, False)
        else:
            perform_calcs(True, False)
        return

    def get_combination_counts(self) -> dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency]]:

        return {
            '1-way': dict(self.one_way_counts),
            '2-way': dict(self.two_way_counts),
            '3-way': dict(self.three_way_counts),
            '4-way': dict(self.four_way_counts),
            '5-way': dict(self.five_way_counts),
            '6-way': dict(self.six_way_counts),
        }

    def get_value_frequencies_and_distinct_values(self) -> tuple[list[Counter[ValueString]], 
            dict[ValueIndex, set[ValueString]]]:

        data = self.data
        distinct_values: dict[int, set[str]] = self.distinct_values
        ncc = len(data[0]) if data else 0
        val_freq:list[Counter[ValueString]] = [Counter() for _ in range(ncc)]

        for row in data:
            for j, value in enumerate(row):
                if value is not None and not pd.isna(value):
                    val_freq[j][value] += 1
                    distinct_values[j].add(value)
        return val_freq, distinct_values

class TrieNode:
    def __init__(self):
        self.children = {}
        self.is_end_of_combo = False
class Trie:
    def __init__(self):
        self.root = TrieNode()

    def insert(self, combo: tuple[ValueCombo_Tuple_index_str, ...]) -> None:
        node = self.root
        for item in sorted(combo, key = lambda x: x[0]): # Sort by index
            if item not in node.children:
                node.children[item] = TrieNode()
            node = node.children[item]
        node.is_end_of_combo = True

    def is_any_subset(self, combo: tuple[ValueCombo_Tuple_index_str, ...]) -> bool:

        def search(node: TrieNode, items: list[ValueCombo_Tuple_index_str], index: int) -> bool:
            if node.is_end_of_combo:
                return True
            if index == len(items):
                return False
            if items[index] in node.children:
                if search(node.children[items[index]], items, index + 1):
                    return True
            return search(node, items, index + 1)

        return search(self.root, sorted(combo), 0)

def find_distinguishing_combos(context: CFDContext, counts_class_a: 
        dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency],
        counts_class_b: dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency], 
        lower_order_distinguishing: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]],
        is_class: bool, t:int, pbar: tq, 
        st: float) -> tuple[bool, list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]], int, int]:

    """
    Finds distinguishing combinations between two classes based on their counts and a distinguishability cutoff.
    It uses a Trie to efficiently check for subsets of combinations that have already been identified as distinguishing
    at a lower t-level.
    It returns a list of distinguishing combinations, the count of unique combinations in class A,
    and the count of non-unique combinations in class A.
    """

    x = context.distinguishability_cutoff
    max_ways = context.max_t_ways
    filter = context.filter

    if t > max_ways:
        return True, [], -1, -1

    if is_class:
        num_rows_class_a = context.nrc
        num_rows_class_b = context.nrn
    else:
        num_rows_class_a = context.nrn
        num_rows_class_b = context.nrc

    distinguishing_combos: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]] = []
    trie = Trie()

    if filter:
        for combo, _, _, _, _ in lower_order_distinguishing:
            trie.insert(combo)

    count_uniq_a = 0
    count_not_uniq_a = 0
    for combo, count_a in counts_class_a.items():
        if st != 0 and time.time() - st > 3:
            return False, [], -1, -1
        pbar.update(1)

        count_b = counts_class_b.get(combo, 0)
        freq_a = count_a / num_rows_class_a
        freq_b = count_b / num_rows_class_b if num_rows_class_b > 0 else 0

        if freq_a >= x * freq_b:
            if filter and not trie.is_any_subset(combo):
                if count_b == 0:
                    count_uniq_a += 1
                else:
                    count_not_uniq_a += 1
                distinguishing_combos.append((combo, freq_a, freq_b, count_a, count_b))
            elif not filter:
                if count_b == 0:
                    count_uniq_a += 1
                else:
                    count_not_uniq_a += 1
                distinguishing_combos.append((combo, freq_a, freq_b, count_a, count_b))
            
    return True, distinguishing_combos, count_uniq_a, count_not_uniq_a

def count_entries_with_distinguishing_combos(context: CFDContext, data: list[list[ValueString]], 
        distin_tway_combos: dict[str, tuple[list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]], ...]], 
        is_nonclass: int) -> list[int]:

    """
    Counts the number of entries in the data that contain distinguishing combinations
    of values up to the specified number of ways (1 to 6).
    """

    max_ways = context.max_t_ways
    logs = context.logs
    silent = context.silenced or context.silenced_ts

    frozen_combos: dict[str, list[frozenset[ValueCombo_Tuple_index_str]]] = {}

    if is_nonclass:
        DVC_row_lst = context.nonclass_row_DVC_occurrence_counts
    else:
        DVC_row_lst = context.class_row_DVC_occurrence_counts

    for t in range(1, max_ways+1):
        frozen_combos[f'{t}-way'] = [frozenset(combo) for combo, _, _, _, _ in distin_tway_combos[f'{t}-way'][is_nonclass]]

    def do_calculation(hide_bar: bool, start: float) -> tuple[bool, list[int]]:

        cl = "Nonclass" if is_nonclass else "Class"
        t_counts: dict[str, int] = {f'{t}-way': 0 for t in range(1, 7)}

        for idx, row in enumerate(tq(data, desc=f"Counting {cl} Distinguishing", disable=hide_bar)):
            if start != 0 and time.time() - start > 3:
                return False, []
            for t in range(1, 7):
                if t > max_ways:
                    break
                row_set = frozenset((index, row[index]) for index in range(len(row)))
                count = sum(combo.issubset(row_set) for combo in frozen_combos[f'{t}-way'])
                DVC_row_lst[idx].append(count)
                if count >= 1:
                    t_counts[f'{t}-way'] += 1
        if is_nonclass:
            context.nonclass_row_DVC_occurrence_counts = DVC_row_lst
        else:
            context.class_row_DVC_occurrence_counts = DVC_row_lst
        return True, [t_counts[f'{t}-way'] for t in range(1, 7)]

    if logs and not silent:
        res = do_calculation(True, time.time())
        if res[0]:
            return res[1]
        DVC_row_lst.clear()
        if is_nonclass:
            DVC_row_lst: dict[int, list[int]] = {i: [] for i in range(context.nrn)}
        else:
            DVC_row_lst: dict[int, list[int]] = {i: [] for i in range(context.nrc)}
        return do_calculation(False, 0)[1]
    else:
        return do_calculation(True, 0)[1]

def generate_DVC_occurrences_CSVs(context: CFDContext):

    DVC_class_row_lst = context.class_row_DVC_occurrence_counts
    DVC_nonclass_row_lst = context.nonclass_row_DVC_occurrence_counts
    nrc = context.nrc
    nrn = context.nrn
    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff
    output = context.output_path

    sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    os.makedirs(sub_dir_name, exist_ok=True)
    new_file_name = f"class_row_DVC_counts.csv"
    file_path = os.path.join(sub_dir_name, new_file_name)
    with open(file_path, 'w',) as file:
        for i in range(nrc):
            file.write(','.join(str(num) for num in DVC_class_row_lst[i]))
            file.write('\n')
        file.close()

    new_file_name = f"nonclass_row_DVC_counts.csv"
    file_path = os.path.join(sub_dir_name, new_file_name)
    with open(file_path, 'w',) as file:
        for i in range(nrn):
            file.write(','.join(str(num) for num in DVC_nonclass_row_lst[i]))
            file.write('\n')
        file.close()

def generate_output_statements(context: CFDContext, 
        class_distinguishing_combos: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]],
        nonclass_distinguishing_combos: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]], 
        t: int) -> None:

    """
    Generates output statements for unique and distinguishing combinations
    based on the provided class and nonclass distinguishing combinations.
    The output is formatted as CSV strings and added to the appropriate file in the context.
    """

    verbose = context.verbose
    variable_names = context.variable_names
    logs = context.logs
    silent = context.silenced or context.silenced_ts
    context.csv_dvc_print_tway[t] = []
    tway_dvc_list = context.csv_dvc_print_tway[t]

    unique_combos: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, str]] = []
    distinguishing_combos_list: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, float]] = []
    total_iter = len(class_distinguishing_combos) + len(nonclass_distinguishing_combos)

    def do_calculation(hide_bar: bool, timeout: bool) -> bool:
        start_time = time.time()

        with tq(total=total_iter, desc=f"{t}-way Calculation Progress", disable=hide_bar) as pbar:
            for combo, freq_class, freq_nonclass, _, _ in class_distinguishing_combos:
                if freq_nonclass == 0:
                    unique_combos.append((combo, freq_class, 'Class'))
                else:
                    distinguishing_combos_list.append(
                        (combo, freq_class, freq_nonclass, freq_class / freq_nonclass))
                pbar.update(1)
                if timeout and time.time() - start_time > 3:
                    return False

            for combo, freq_nonclass, freq_class, _, _ in nonclass_distinguishing_combos:
                if freq_class == 0:
                    unique_combos.append((combo, freq_nonclass, 'Nonclass'))
                else:
                    distinguishing_combos_list.append(
                        (combo, freq_class, freq_nonclass, freq_nonclass / freq_class))
                pbar.update(1)
                if timeout and time.time() - start_time > 3:
                    return False
        return True

    if logs and not silent:
        if not do_calculation(True, True):
            unique_combos.clear()
            distinguishing_combos_list.clear()
            do_calculation(False, False)
    else:
        do_calculation(True, False)

    # Sort unique combos by frequency in the respective file
    unique_combos.sort(key=lambda x: x[1], reverse=True)

    # NOTE: Sort distinguishing combos by frequency difference in decreasing order
    # distinguishing_combos_list.sort(key=lambda x: x[3], reverse=True) # (uncomment this to use this ordering instead)

    # Sort distinguishing combos by frequency in the respective file 
    # NOTE: (comment this out when using the other ordering )
    distinguishing_combos_list.sort(key=lambda x: max(x[1], x[2]), reverse=True) 

    total_iter = len(unique_combos) + len(distinguishing_combos_list)

    def do_appending(hide_bar: bool, timeout: bool) -> bool:
        start_time = time.time()

        with tq(total=total_iter, desc=f"{t}-way DVC Progress", disable=hide_bar) as pbar:
            for combo, freq, class_type in unique_combos:
                i = 1 if class_type == "Class" else 0
                if not verbose:
                    csv_str = ";".join(f"({index}, {value})" for index, value in combo)
                    tway_dvc_list.append(f"U;{i};{csv_str};{freq:.4f};;")
                else:
                    csv_str = ";".join(f"({variable_names[cast(int, index)]}, {value})" for index, value in combo)
                    tway_dvc_list.append(f"U;{i};{csv_str};{freq:.4f};;")
                pbar.update(1)
                if timeout and time.time() - start_time > 3:
                    return False

            for combo, freq_a, freq_b, diff in distinguishing_combos_list:
                h_freq = freq_a if freq_a > freq_b else freq_b
                i = 1 if freq_a > freq_b else 0

                if not verbose:
                    csv_str = ";".join(f"({index}, {value})" for index, value in combo)
                    tway_dvc_list.append(f"D;{i};{csv_str};{h_freq:.4f};{diff:.4f};")
                else:
                    csv_str = ";".join(f"({variable_names[index]}, {value})" for index, value in combo)
                    tway_dvc_list.append(f"D;{i};{csv_str};{h_freq:.4f};{diff:.4f};")
                pbar.update(1)
                if timeout and time.time() - start_time > 3:
                    return False
            return True

    if logs and not silent:
        if not do_appending(True, True):
            tway_dvc_list.clear()
            do_appending(False, False)
    else:
        do_appending(True, False)

def calculate_max_possible_t_interactions(context: CFDContext, distinct_values: dict[ValueIndex, set[ValueString]], 
        t: int, st: float, pbar: tq) -> tuple[bool, int, dict[tuple[ValueIndex, ...], list[tuple[ValueString, ...]]]]:

    """
    Calculates the maximum number of t-way combinations possible given the distinct values for each variable.
    It returns the maximum number of combinations and a dictionary of all possible t-way combinations.
    """

    max_ways = context.max_t_ways

    if t > max_ways:
        return True, -1, {}

    max_tway_combos: int = 0
    all_possible_tway_combos: dict[tuple[ValueIndex, ...], list[tuple[ValueString, ...]]] = {}

    # Only include keys with non-empty value sets to ensure CSVs with missing data are properly handled.
    valid_keys = [k for k, v in distinct_values.items() if v]

    for combo in combinations(valid_keys, t):
        if st != 0 and time.time() - st > 3:
            return False, -1, {}
        pbar.update(1)
        values_product = list(product(*(distinct_values[combo[j]] for j in range(t))))

        max_tway_combos += len(values_product)
        all_possible_tway_combos[combo] = values_product

    return True, max_tway_combos, all_possible_tway_combos

def count_common_combinations(context: CFDContext, 
        counts_class: dict[str,dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency]],
        counts_nonclass: dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency]]) -> dict[str, int]:

    """
    Counts the number of common combinations between class and nonclass counts
    for 1-way to 6-way combinations.
    Returns a dictionary with the counts for each way. 
    """

    max_ways = context.max_t_ways

    common_dict: dict[str, int] = {f'{t}-way': 0 for t in range(1, 7)}

    for t in range(1, max_ways+1):
        common_dict[f'{t}-way'] = len(set(counts_class[f'{t}-way']) & set(counts_nonclass[f'{t}-way']))

    return common_dict

def find_missing_combos(context: CFDContext, 
        all_possible_tway_union: dict[tuple[ValueIndex, ...], list[tuple[ValueString, ...]]], t: int, 
        all_possible_tway_class: dict[tuple[ValueIndex, ...], list[tuple[ValueString, ...]]],
        all_possible_tway_nonclass: dict[tuple[ValueIndex, ...], list[tuple[ValueString, ...]]]) -> tuple[
        list[tuple[tuple[str, ...], list[int]]],
        list[tuple[tuple[str, ...], list[int]]],
        list[tuple[tuple[str, ...], list[int]]]]:

    """
    Finds missing t-way combinations in the class and nonclass data
    based on the provided all_possible_tway_class and all_possible_tway_nonclass dictionaries.
    Returns two lists: one for missing class combinations and one for missing nonclass combinations.
    If the context is set to skip producing MVCs or if t exceeds the maximum t-way allowed, it returns empty lists.
    """

    combination_counts_class = context.combination_counts_class
    combination_counts_nonclass = context.combination_counts_nonclass
    logs = context.logs
    silent = context.silenced or context.silenced_ts
    missing_internal: dict[str, dict[tuple[tuple[int, str], ...], tuple[bool, bool]]] = context.missing_internally_all_tways
    mics = context.missing_internal_counts

    mics[f'{t}-way'] = [0] * 12
    missing_internal[f'{t}-way'] = {}
    cur_missing_dict = missing_internal[f'{t}-way']
    if not context.gen_mvcs or t > context.max_t_ways:
        return [], [], []

    missing_tway_class: list[tuple[tuple[ValueString, ...], list[ValueIndex]]] = []
    missing_tway_nonclass: list[tuple[tuple[ValueString, ...], list[ValueIndex]]] = []
    missing_tway_union: list[tuple[tuple[ValueString, ...], list[ValueIndex]]] = []

    def is_valid_combo(values: tuple[str, ...]) -> bool:

        """
        Checks if all values in the combination are not null.
        Returns True if all values are not null, otherwise False.
        """
        return all(pd.notnull(v) for v in values)

    def sort(combo: tuple[ValueCombo_Tuple_index_str, ...]) -> tuple[ValueCombo_Tuple_index_str, ...]:

        """
        Standardizes the combination by sorting it based on the first element of each tuple.
        """

        ret = tuple(sorted(combo, key=lambda x: x[0]))
        return ret

    norm_class_t = {sort(c) for c in combination_counts_class[f'{t}-way']}
    norm_nonclass_t = {sort(c) for c in combination_counts_nonclass[f'{t}-way']}

    total_iters = 0
    for _, values_list in all_possible_tway_union.items():
        total_iters += len(values_list)

    def do_calculation(hide_bar: bool, timeout: bool) -> tuple[bool, 
            list[tuple[tuple[ValueString, ...], list[ValueIndex]]], 
            list[tuple[tuple[ValueString, ...], list[ValueIndex]]],
            list[tuple[tuple[ValueString, ...], list[ValueIndex]]]]:

        pbar = tq(total=total_iters, desc=f"{t}-way MVCs", disable=hide_bar)
        missing_tway_class.clear()
        missing_tway_nonclass.clear()
        missing_tway_union.clear()
        start_time = time.time()
        cur_missing_dict.clear()
        mics[f'{t}-way'] = [0] * 12
        cur_mics = mics[f'{t}-way']
        for indices, values_list in all_possible_tway_union.items():
            for values in values_list:
                if timeout and time.time() - start_time > 3:
                    return False, [], [], []
                pbar.update(1)
                if not is_valid_combo(values):
                    continue
                combo = tuple(zip(indices, values))
                missing_from_class = False
                missing_from_nonclass = False
                can_be_made_with_just_class = False
                can_be_made_with_just_nonclass = False
                srt_combo = sort(combo)
                if indices in all_possible_tway_class:
                    cl_values_lst = all_possible_tway_class[indices]
                    if values in cl_values_lst:
                        can_be_made_with_just_class = True
                if indices in all_possible_tway_nonclass:
                    nc_values_lst = all_possible_tway_nonclass[indices]
                    if values in nc_values_lst:
                        can_be_made_with_just_nonclass = True
                if srt_combo not in norm_class_t:
                    missing_from_class = True
                if srt_combo not in norm_nonclass_t:
                    missing_from_nonclass = True
                if missing_from_class and missing_from_nonclass:
                    missing_tway_union.append((values, list(indices)))
                elif missing_from_class:
                    missing_tway_class.append((values, list(indices)))
                elif missing_from_nonclass:
                    missing_tway_nonclass.append((values, list(indices)))
                if missing_from_class or missing_from_nonclass:
                    cur_missing_dict[combo] = (can_be_made_with_just_class, can_be_made_with_just_nonclass)

                if missing_from_class and missing_from_nonclass:
                    if can_be_made_with_just_class and can_be_made_with_just_nonclass:
                        cur_mics[8] += 1
                    elif can_be_made_with_just_class:
                        cur_mics[9] += 1
                    elif can_be_made_with_just_nonclass:
                        cur_mics[10] += 1
                    else:
                        cur_mics[11] += 1
                elif missing_from_class:
                    if can_be_made_with_just_class and can_be_made_with_just_nonclass:
                        cur_mics[0] += 1
                    elif can_be_made_with_just_class:
                        cur_mics[1] += 1
                    elif can_be_made_with_just_nonclass:
                        cur_mics[2] += 1
                    else:
                        cur_mics[3] += 1
                elif missing_from_nonclass:
                    if can_be_made_with_just_class and can_be_made_with_just_nonclass:
                        cur_mics[4] += 1
                    elif can_be_made_with_just_class:
                        cur_mics[5] += 1
                    elif can_be_made_with_just_nonclass:
                        cur_mics[6] += 1
                    else:
                        cur_mics[7] += 1
        return True, missing_tway_class, missing_tway_nonclass, missing_tway_union

    res: tuple[bool, list[tuple[tuple[ValueString, ...], list[ValueIndex]]], 
               list[tuple[tuple[ValueString, ...], list[ValueIndex]]],
               list[tuple[tuple[ValueString, ...], list[ValueIndex]]]] = (True, [], [], [])
    if logs and not silent:
        res = do_calculation(True, True)
        if not res[0]:
            res = do_calculation(False, False)
    else:
        res = do_calculation(True, False)
        
    return res[1], res[2], res[3]

def find_common_entries(context: CFDContext) -> list[tuple[tuple[str, ...], dict[str, int]]]:

    """
    Find entries that appear in both class and nonclass files, and record their counts.
    """

    class_file_data = context.class_file_data
    nonclass_file_data = context.nonclass_file_data
    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff
    output = context.output_path
    drop_ce = context.drop_common.lower()
    if drop_ce not in ['all', 'both', 'class', 'nonclass']:
        drop_ce = 'none'
    if drop_ce == 'both':
        drop_ce = 'all'
    # Count entries in class data
    class_counts: dict[tuple[str, ...], int] = defaultdict(int)
    for entry in class_file_data:
        class_counts[tuple(entry)] += 1

    # Count entries in nonclass data
    nonclass_counts: dict[tuple[str, ...], int] = defaultdict(int)
    for entry in nonclass_file_data:
        nonclass_counts[tuple(entry)] += 1

    # Find common entries and their counts
    common_entries: list[tuple[tuple[str, ...], dict[str, int]]] = []
    for entry in class_counts:
        if entry in nonclass_counts:
            common_entries.append(
                (entry,
                {'class_count': class_counts[entry],
                 'nonclass_count': nonclass_counts[entry]}
            ))

    if common_entries:
        plural = ("entry", "it", "has", "row") if len(common_entries) == 1 else ("entries", "them", "have", "rows")
        if drop_ce == 'none':
            print_warning_message(context, f"Found {len(common_entries)} common {plural[0]} between class and nonclass " \
                f"files. To view {plural[1]}, check the info.txt output file")

        def remove_all(context: CFDContext, cl: bool, entry: list[str]) -> None:

            if cl:
                new_cl = [row for row in context.class_file_data if row != entry]
                context.class_file_data = new_cl
            else:
                new_nc = [row for row in context.nonclass_file_data if row != entry]
                context.nonclass_file_data = new_nc
        if drop_ce.lower() != 'none':
            num_removed = 0
            for entry, _ in common_entries:
                if drop_ce.lower() == 'class' or drop_ce.lower() == 'all':
                    num_removed += context.class_file_data.count(list(entry))
                    remove_all(context, True, list(entry))
                if drop_ce.lower() == 'nonclass' or drop_ce.lower() == 'all':
                    num_removed += context.nonclass_file_data.count(list(entry))
                    remove_all(context, False, list(entry))
            pl2 = ['rows', 'were'] if num_removed > 1 else ['row', 'was']
            if drop_ce != 'all':
                print_info_message(context, f"{len(common_entries)} unique common {plural[3]} {plural[2]} been dropped " \
                    f"from the {drop_ce} file. To view {plural[1]}, see info.txt.\nIn total, " \
                    f"{num_removed} {pl2[0]} {pl2[1]} dropped")
            else:
                print_info_message(context, f"{len(common_entries)} unqiue common {plural[3]} {plural[2]} been dropped " \
                    f"from both files. To view {plural[1]}, see info.txt.\nIn total, " \
                    f"{num_removed} {pl2[0]} {pl2[1]} dropped between both files")

        context.nrc = len(context.class_file_data)
        context.nrn = len(context.nonclass_file_data)
        sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
        os.makedirs(sub_dir_name, exist_ok=True)
        new_file_name = f"common_entries.csv"
        file_path = os.path.join(sub_dir_name, new_file_name)
        with open(file_path, 'w',) as file:
            file.write("Entry;Class_Count;Nonclass_Count\n")
            for entry, counts in common_entries:
                entry_str = "(" + ",".join(str(value) for value in entry) + ")"
                file.write(f"{entry_str};{counts['class_count']};{counts['nonclass_count']}\n")
            file.close()
    elif drop_ce.lower() != 'none':
        print_info_message(context, "No common entries detected")
    return common_entries

def safe_set_ylim(ax: mpl_axes.Axes, values: list[float], pad_edges: bool) -> None:

    """
    Safely sets the y-axis limits for a given axis object.
    If the minimum and maximum values are equal, it adds a small buffer to avoid singular transformation.
    """

    y_min = min(values)
    y_max = max(values)
    data_range = y_max - y_min
    padding = data_range * 0.1

    graph_y_min = y_min
    graph_y_max = y_max

    if y_min > 0:
        graph_y_min = 0
    elif y_min == 0:
        if pad_edges:
            graph_y_min = -1 * padding
    else:
        graph_y_min = y_min - padding
    if y_max < 0:
        graph_y_max = 0
    elif y_max == 0:
        if pad_edges:
            graph_y_max = padding
    else:
        graph_y_max = y_max + padding

    if data_range == 0:
        padding = 0.1
        y_min -= padding
        graph_y_min = y_min
        y_max += padding
        graph_y_max = y_max

    num_ticks = 5
    tick_range = y_max - y_min
    tick_interval_approx = tick_range / (num_ticks - 1)

    # Determine the precision needed for the tick interval
    precision = -int(np.floor(np.log10(tick_interval_approx))) if tick_interval_approx != 0 else 0
    tick_interval = round(tick_interval_approx, precision)

    # Adjust the tick interval to be "nicer" (ex, 0.1, 0.2, 0.25, 0.5, 1)
    if tick_interval_approx != 0:
        order_of_magnitude = 10 ** (-precision)
        if tick_interval > 5 * order_of_magnitude:
            tick_interval = 10 * order_of_magnitude
        elif tick_interval > 2 * order_of_magnitude:
            tick_interval = 5 * order_of_magnitude
        elif tick_interval > order_of_magnitude:
            tick_interval = 2 * order_of_magnitude
        else:
            tick_interval = order_of_magnitude

    precision = -int(np.floor(np.log10(tick_interval))) if tick_interval != 0 else 0

    # Calculate the first tick position
    first_tick = np.ceil(y_min / tick_interval) * tick_interval

    # Generate the ticks
    ticks = [first_tick + i * tick_interval for i in range(num_ticks)]

    # Filter ticks to be within the y_min and y_max, sort them, remove dups, then round to remove floating point errors
    filtered_ticks = [tick for tick in ticks if y_min <= tick <= y_max]
    filtered_ticks = sorted(list(set(filtered_ticks)))
    filtered_ticks = [round(tick, precision) for tick in filtered_ticks]

    # Ensure that y_min and y_max are in the ticks
    if y_min not in filtered_ticks:
        # If they're not, check whether to replace the top/bottom most tick with the max/min, or to just add them
        # Give a bit more precision to the y_max and y_min ticks so that the user can better see the max/min of the data
        if abs(filtered_ticks[0] - y_min) > tick_interval * 0.5:
            filtered_ticks.insert(0, round(y_min, precision+1))
        else:
            filtered_ticks[0] = round(y_min, precision+1)
    if y_max not in filtered_ticks:
        if abs(filtered_ticks[-1] - y_max) > tick_interval * 0.5:
            filtered_ticks.append(round(y_max, precision+1))
        else:
            filtered_ticks[-1] = round(y_max, precision+1)
    ax.set_ylim(graph_y_min, graph_y_max)
    ax.set_yticks(filtered_ticks)

def safely_step_graph(ax: mpl_axes.Axes, data: list[float], lbl:str, clr: str, name: str="", alp: float=1.0, xaxis=[]) -> bool:

    """
    Ensure that a potential memory error is handled when generating step graphs. If an error is caught,
    floats will be downgraded from `float64` to `float32`, and then again to `float16` upon a second failure.
    """

    if len(xaxis) == 0:
        xaxis = range(len(data))
    try:
        ax.step(xaxis, data, color=clr, label=f'{lbl} {name}', alpha=alp, where='mid')
    except MemoryError:
        downgrade = "float32"
        try:
            new_data = np.array(data, dtype=np.float32)
            data = cast(list[float], new_data)
            ax.step(xaxis, data, color=clr, label=f'{lbl} {name}', alpha=alp, where='mid')
        except MemoryError:
            downgrade = "float16"
            try:
                new_data = np.array(data, dtype=np.float16)
                data = cast(list[float], new_data)
                ax.step(xaxis, data, color=clr, label=f'{lbl} {name}', alpha=alp, where='mid')
            except MemoryError as ex:
                print_warning_message(context, f"Could not generate {lbl} graph due to insufficient memory.\nException: {ex}")
                return False
        print_warning_message(context, f"Your floats have been downgraded from float64 to {downgrade} in order to " \
            "preserve RAM when step-graphing (you ran out)")
    return True

def analyze_combos(context: CFDContext, 
        counts_class_a: dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency]], 
        counts_class_b: dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency]]) -> tuple[list[float], 
        list[float], list[float]]:

    """
    Analyzes the relative frequencies and occurrences of combinations in two classes and generates graphs if enabled.
    Returns the differences in relative frequencies for each combination.
    """

    gen_graphs = context.gen_graphs
    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff
    nrc, nrn = context.nrc, context.nrn
    max_ways = context.max_t_ways
    logs = context.logs
    silent = context.silenced or context.silenced_ts
    output = context.output_path

    freq_cl: list[float] = []
    freq_nc: list[float] = []
    freq_u: list[float] = []
    occur_cl: list[float] = []
    occur_nc: list[float] = []
    occur_u: list[float] = []
    num_each_t_way: list[int] = [] # cumulative count
    total_iters: int = 0

    if logs:
        for r in range(1, max_ways+1):
            key = f'{r}-way'
            all_combos = set(counts_class_a[key].keys()).union(
                counts_class_b[key].keys())
            total_iters += len(all_combos)
            num_each_t_way.append(total_iters)

    def do_calculation(hide_bar: bool, timeout: bool) -> bool:

        start_time = time.time()
        with tq(total=total_iters, desc='Combo Analysis', disable=hide_bar) as pbar:
            for r in range(1, max_ways+1):
                key = f'{r}-way'
                all_combos = set(counts_class_a[key].keys()).union(counts_class_b[key].keys())
                for combo in all_combos:
                    count_a = counts_class_a[key].get(combo, 0)
                    count_b = counts_class_b[key].get(combo, 0)
                    freq_a = count_a / nrc if nrc > 0 else 0
                    freq_b = count_b / nrn if nrn > 0 else 0

                    df = freq_a - freq_b
                    freq_u.append(df)
                    freq_cl.append(freq_a)
                    freq_nc.append(freq_b)
                    occur_cl.append(count_a)
                    occur_nc.append(count_b)
                    occur_u.append(count_a - count_b)

                    pbar.update(1)
                    if timeout and time.time() - start_time > 3:
                        return False
            return True
    if logs and not silent:
        if not do_calculation(True, True):
            freq_u.clear()
            freq_cl.clear()
            freq_nc.clear()
            occur_cl.clear()
            occur_nc.clear()
            occur_u.clear()
            do_calculation(False, False)
    else:
        do_calculation(True, False)

    if gen_graphs:

        def make_graph(cl: list[float], nc: list[float], un:list[float], name: str) -> None:

            """
            This function is responsible for making the Relative_Frequencies and Relative_Occurrences graphs.
            These graphs represent the frequency / occurrence of ALL t-way value combinations from t=1 to t=max set.
            These include both Unique, Distinguishning, and Non-Distinguishing combinations.
            They are ordered by t-size.
            """

            fig, (ax1, ax2, ax3) = plt.subplots(3, 1, figsize=(18, 15))
            ax1 = cast(mpl_axes.Axes, ax1)
            ax2 = cast(mpl_axes.Axes, ax2)
            ax3 = cast(mpl_axes.Axes, ax3)
            fig.subplots_adjust(hspace=0.5)

            if cl:
                cl = [cl[0]] + cl + [cl[-1]] # These are done so that the steps extend to the graph edges
            if nc:
                nc = [nc[0]] + nc + [nc[-1]] # Only really noticible for very small datasets
            if un:
                un = [un[0]] + un + [un[-1]] # The duplicated values are ignored in the display and calculations

            def set_the_x_axis(ax: mpl_axes.Axes, lst: list[float]):
                current_xticks: list[int] = []
                tick_labels: list[str] = []
                max_num = max(num_each_t_way) if num_each_t_way else 0
                for t, pos in enumerate(num_each_t_way):
                    current_xticks.append(pos)
                    if t != 0 and current_xticks[t] - current_xticks[t-1] < max_num * 0.04:
                        if t != 1 and current_xticks[t] - current_xticks[t-2] < max_num * 0.04:
                            tick_labels.append(f"\n\n\n\n{t+1}-way\n{pos}")
                        else:
                            tick_labels.append(f"\n\n{t+1}-way\n{pos}")
                    else:
                        tick_labels.append(f"{t+1}-way\n{pos}")
                    ax.axvline(pos, color='black', linestyle='-', alpha=0.5, linewidth=2)
                ax.set_xticks(current_xticks, tick_labels)
                ax.tick_params(
                    axis='x',
                    which='both',
                    bottom=True,
                    top=False,
                    grid_linewidth = 2
                )
                ax.set_xlim(0.5, len(lst)-1.5)

            print_timestamp_message(context, f"Generating Class Value Combo {name} Graph")

            success = safely_step_graph(ax1, cl, 'Class', 'blue', name, 0.7)
            if success:
                ax1.set_title(f'Class {name} for All T-Way Combos')
                set_the_x_axis(ax1, cl)
                ax1.set_ylabel(f'{name}')
                ax1.legend(loc='best')
                ax1.grid(axis='y')
                if cl:
                    safe_set_ylim(ax1, cl, False)
            else:
                ax1.set_axis_off()
            print_timestamp_message(context, f"Generating Nonclass Value Combo {name} Graph")
            success = safely_step_graph(ax2, nc, 'Nonclass', 'red', name, 0.7)
            if success:
                ax2.set_title(f'Nonclass {name} for All T-Way Combos')
                set_the_x_axis(ax2, nc)
                ax2.set_ylabel(f'{name}')
                ax2.legend(loc='best')
                ax2.grid(axis='y')
                if nc:
                    safe_set_ylim(ax2, nc, False)
            else:
                ax2.set_axis_off()
            print_timestamp_message(context, f"Generating Difference Value Combo {name} Graph")

            success = safely_step_graph(ax3, un, 'Difference of Class and Nonclass', 'purple', name, 0.7)
            if success:
                ax3.set_title(f'Difference of {name} (Class - Nonclass) for All T-way Combos')
                set_the_x_axis(ax3, un)
                ax3.set_ylabel(f'Diff of {name}')
                ax3.legend(loc='best')
                ax3.grid(axis='y')
                if freq_u:
                    safe_set_ylim(ax3, un, False)
                ax3.axhline(0, color='black', linestyle='-', linewidth=2.5)
            else:
                ax3.set_axis_off()
            sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
            graphs_dir = os.path.join(sub_dir_name, "Graphs")
            os.makedirs(graphs_dir, exist_ok = True)
            file_name = os.path.join(graphs_dir, f"value_combo_{name.lower()}.png")
            plt.savefig(file_name, dpi = 300, bbox_inches = 'tight')
            plt.close(fig)

        make_graph(freq_cl, freq_nc, freq_u, "Frequencies")
        make_graph(occur_cl, occur_nc, occur_u, "Occurrences")

    return freq_u, freq_cl, freq_nc

def distinguishing_coverage_graph(context: CFDContext, t: int) -> None:

    """
    Generates a graph showing the distinguishing coverage for class and nonclass combinations.
    This function plots the frequencies of distinguishing combinations for both class and nonclass data,
    and the difference between them. It saves the graph to a file in the Graphs directory.
    """

    gen_graphs = context.gen_graphs
    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff
    max_ways = context.max_t_ways
    output = context.output_path

    if t > max_ways or not gen_graphs:
        return

    distinguishing_class_combos = context.distin_tway_combos[f"{t}-way"][0]
    distinguishing_nonclass_combos = context.distin_tway_combos[f"{t}-way"][1]

    # Extract the combos and their frequencies
    class_combos: dict[tuple[tuple[int, str], ...], tuple[float, float, int, int]] = {combo: (freq_a, freq_b, count_a, count_b)
        for combo, freq_a, freq_b, count_a, count_b in distinguishing_class_combos}
    nonclass_combos: dict[tuple[tuple[int, str], ...], tuple[float, float, int, int]] = {combo: (freq_a, freq_b, count_a, count_b)
        for combo, freq_a, freq_b, count_a, count_b in distinguishing_nonclass_combos}

    freq_cl: list[float] = []
    freq_nc: list[float] = []
    freq_u: list[float] = []
    num_cl: list[float] = []
    num_nc: list[float] = []
    num_u: list[float] = []

    all_combos = set(class_combos.keys()).union(nonclass_combos.keys())

    for combo in all_combos:
        freq_a_class, freq_a_nonclass, count_cl_a, count_nc_a = class_combos.get(combo, (0, 0, 0, 0))
        freq_b_nonclass, freq_b_class, count_nc_b, count_cl_b = nonclass_combos.get(combo, (0, 0, 0, 0))

        freq_class = max(freq_a_class, freq_b_class)
        freq_nonclass = max(freq_a_nonclass, freq_b_nonclass)
        num_class = max(count_cl_a, count_cl_b)
        num_nonclass = max(count_nc_a, count_nc_b)

        freq_cl.append(freq_class)
        freq_nc.append(freq_nonclass)
        freq_u.append(freq_class - freq_nonclass)

        num_cl.append(num_class)
        num_nc.append(num_nonclass)
        num_u.append(num_class - num_nonclass)

    if freq_cl:
        freq_cl = [freq_cl[0]] + freq_cl + [freq_cl[-1]]
        num_cl = [num_cl[0]] + num_cl + [num_cl[-1]]
    if freq_nc:
        freq_nc = [freq_nc[0]] + freq_nc + [freq_nc[-1]]
        num_nc = [num_nc[0]] + num_nc + [num_nc[-1]]
    if freq_u:
        freq_u = [freq_u[0]] + freq_u + [freq_u[-1]]
        num_u = [num_u[0]] + num_u + [num_u[-1]]

    def set_the_x_axis(ax: mpl_axes.Axes, lst: list[float]):
        ax.set_xlabel('Distinguishing Value Combos')
        current_xticks: list[int] = []
        tick_labels: list[str] = []

        if len(lst) > 10:
            diff = len(lst) / 5
            for i in range(0, 5):
                current_xticks.append(int(i + diff*i))
            current_xticks.append(len(lst)-2)
            tick_labels = [str(j) for j in current_xticks]
        else:
            current_xticks = [i for i in range(len(lst))]
            tick_labels = [str(current_xticks[i]) for i in range(len(lst))]
        ax.set_xticks(current_xticks, tick_labels)
        ax.tick_params(
            axis='x',
            which='both',
            bottom=True,
            top=False,
        )
        ax.set_xlim(0.5, len(lst)-1.5)

    if gen_graphs:
        print_timestamp_message(context, f"Generating {t}-way coverage graphs")

        def generate_graphs(cl: list[float], nc: list[float], un: list[float], name: str) -> None:

            """
            Create the Distinguishing T-Way Frequency and Occurrences graphs
            """

            fig, (ax1, ax2, ax3) = plt.subplots(3, 1, figsize = (18, 9))
            ax1 = cast(mpl_axes.Axes, ax1)
            ax2 = cast(mpl_axes.Axes, ax2)
            ax3 = cast(mpl_axes.Axes, ax3)
            fig.subplots_adjust(hspace=0.5)
            
            success = safely_step_graph(ax1, cl, 'Class', 'blue', name, 1)
            if success:
                ax1.set_title(f'Class {name} for Distinguishing {t}-way Combos')
                set_the_x_axis(ax1, cl)
                ax1.set_ylabel(f'{name}')
                ax1.legend(loc='best')
                ax1.grid(True, which='major', linestyle='--', linewidth=0.5)
                if cl:
                    safe_set_ylim(ax1, cl, True)
            else:
                ax1.set_axis_off()

            success = safely_step_graph(ax2, nc, 'Nonclass', 'red', name, 1)
            if success:
                ax2.set_title(f'Nonclass {name} for Distinguishing {t}-way Combos')
                set_the_x_axis(ax2, nc)
                ax2.set_ylabel(f'{name}')
                ax2.legend(loc='best')
                ax2.grid(True, which='major', linestyle='--', linewidth=0.5)
                if nc:
                    safe_set_ylim(ax2, nc, True)
            else:
                ax2.set_axis_off()

            success = safely_step_graph(ax3, un, 'Difference of', 'purple', name, 1)
            if success:
                ax3.set_title(f'Difference in {name} (Class - Nonclass) for Distinguishing {t}-way Combos')
                set_the_x_axis(ax3, un)
                ax3.set_ylabel(f'Diff of {name}')
                ax3.legend(loc='best')
                ax3.grid(True, which='major', linestyle='--', linewidth=0.5)
                if un:
                    safe_set_ylim(ax3, un, True)
                ax3.axhline(0, color='black', linestyle='-', linewidth=2.5)
            else:
                ax3.set_axis_off()
            sub_dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
            graphs_dir = os.path.join(sub_dir_name, "Graphs")
            os.makedirs(graphs_dir, exist_ok=True)
            sub_dir_freq = os.path.join(graphs_dir, f"Distinguishing {name}")
            os.makedirs(sub_dir_freq, exist_ok=True)
            file_name = os.path.join(sub_dir_freq, f"distinguishing_{name.lower()}_{t}_way.png")
            plt.savefig(file_name, dpi = 300, bbox_inches = 'tight')
            plt.close(fig)

        generate_graphs(freq_cl, freq_nc, freq_u, "Frequencies")
        generate_graphs(num_cl, num_nc, num_u, "Occurrences")

def filter_distinguishing(context: CFDContext, 
        combination_counts: dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], int]], 
        distinguishing_combos: dict[str, list[tuple[tuple[ValueCombo_Tuple_index_str, ...], 
        float, float, int, int]]]) -> dict[int, dict[tuple[ValueCombo_Tuple_index_str, ...], int]]:

    """ 
    Filters the distinguishing combinations based on the provided combination counts.
    It checks if each distinguishing combination exists in the combination counts for each way
    and returns a dictionary with the counts of distinguishing combinations for each way.
    """

    distinguishing_counts: dict[int, dict[tuple[ValueCombo_Tuple_index_str, ...], int]] = {}
    for t in range(1, 7):
        distinguishing_counts[t] = {}

    for t in range(1, 7):
        for combo, _, _, _, _ in distinguishing_combos[f'{t}-way']:
            try:
                distinguishing_counts[t][combo] = combination_counts[f'{t}-way'][combo]
            except Exception as ex:
                print_warning_message(context, f"Something went wrong when filtering distinguishing combinations. " \
                    f"One of DVCs, {combo}, does not have any data associated with it.\nProgram will continue, but " \
                    f"be warned that results are likely compromised.\nException Caught: {ex}")
    return distinguishing_counts

def aggregate_counts_by_variable_distinguishing(context: CFDContext, 
        distinguishing_combination_counts: dict[int, dict[tuple[ValueCombo_Tuple_index_str, ...],
        int]]) -> list[list[int]]:

    """
    Aggregates the counts of distinguishing combinations by variable index.
    It returns lists of counts for 1-way to 6-way combinations, where each list 
    contains counts for each variable index.
    """

    ncc = context.ncc
    max_ways = context.max_t_ways

    counts = {t: [0] * ncc for t in range(1, 7)}

    for t in range(1, 7):
        if t > max_ways:
            break
        for key, _ in distinguishing_combination_counts[t].items():
            for idx in range(t):
                counts[t][key[idx][0]] += 1

    return [counts[t] for t in range(1, 7)]

def merge_combination_counts(counts_class: dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency]], 
        counts_nonclass: dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency]]) -> dict[
        str, dict[tuple[ValueCombo_Tuple_index_str, ...], int]]:

    """
    Merges the combination counts from class and nonclass data.
    It combines the counts for each way (1-way to 6-way) from both class and nonclass counts.
    Returns a dictionary with the merged counts for each way.
    """

    merged_counts = cast(dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], int]], defaultdict(lambda: defaultdict(int)))

    for key in counts_class:
        for combo, count in counts_class[key].items():
            merged_counts[key][combo] += count

    for key in counts_nonclass:
        for combo, count in counts_nonclass[key].items():
            merged_counts[key][combo] += count

    return merged_counts

def get_tway_coverage_graphs(context: CFDContext) -> None:

    """
    Generates graphs showing the coverage of t-way combinatorial value combinations (VCs).
    It plots the coverage percentages for class and nonclass VCs out of maximum possible VCs
    for each t-way level, and saves the graphs to the main run's folder.
    The graphs include:
    - Class coverage out of maximum union VCs
    - Class coverage out of maximum class VCs
    - Nonclass coverage out of maximum union VCs
    - Nonclass coverage out of maximum nonclass VCs
    - Union coverage out of maximum union VCs
    """

    max_ways = context.max_t_ways
    grid = cast(list[list[int]], context.data['grid'])
    output = context.output_path

    t_levels = np.arange(1, max_ways + 1)
    t_levels_ext = np.arange(0, max_ways + 2)

    # Prepare data for each graph
    max_union = [grid[i][0] for i in range(max_ways)]
    max_class = [grid[i][1] for i in range(max_ways)]
    max_nonclass = [grid[i][2] for i in range(max_ways)]
    present_class = [grid[i][3] for i in range(max_ways)]
    present_nonclass = [grid[i][4] for i in range(max_ways)]
    present_intersect = [grid[i][5] for i in range(max_ways)]

    # Coverage percentages
    percent_cl_of_max_cl = [
        (present_class[i] / max_class[i] * 100) if max_class[i] != 0 else 0
        for i in range(max_ways)
    ]
    percent_cl_of_max_cl_ext = [percent_cl_of_max_cl[0]] + percent_cl_of_max_cl + [percent_cl_of_max_cl[-1]]

    percent_nc_of_max_nc = [
        (present_nonclass[i] / max_nonclass[i] * 100) if max_nonclass[i] != 0 else 0
        for i in range(max_ways)
    ]
    percent_nc_of_max_nc_ext = [percent_nc_of_max_nc[0]] + percent_nc_of_max_nc + [percent_nc_of_max_nc[-1]]

    percent_cl_of_all = [
        (present_class[i] / max_union[i] * 100) if max_union[i] != 0 else 0
        for i in range(max_ways)
    ]
    percent_cl_of_all_ext = [percent_cl_of_all[0]] + percent_cl_of_all + [percent_cl_of_all[-1]]

    percent_nc_of_all = [
        (present_nonclass[i] / max_union[i] * 100) if max_union[i] != 0 else 0
        for i in range(max_ways)
    ]
    percent_nc_of_all_ext = [percent_nc_of_all[0]] + percent_nc_of_all + [percent_nc_of_all[-1]]

    percent_union = [
        ((present_class[i] + present_nonclass[i] - present_intersect[i]) / max_union[i] * 100) 
        if max_union[i] != 0 else 0
        for i in range(max_ways)
    ]
    percent_union_ext = [percent_union[0]] + percent_union + [percent_union[-1]]
    # _ext data structure extensions are so that the lines on the resulting graphs extend to the edges

    # Plotting
    fig, axs = plt.subplots(3, 2, figsize=(10, 12), sharex='none')
    fig.suptitle("T-Way Combinatorial Value Combination (VC) Coverage")
    fig.subplots_adjust(hspace=0.4)
    y_ticks = np.arange(0, 105, 10)
    x_ticks = t_levels
    axs = cast(list[list[mpl_axes.Axes]], axs)

    fails: list[list[bool]] = [[False, False], [False, False], [False, True]]

    # Class coverage out of max all ways
    success = safely_step_graph(axs[0][0], percent_cl_of_all_ext, "Class Coverage", 'blue', xaxis=t_levels_ext)
    if success:
        axs[0][0].set_ylabel('Class Coverage (%)')
        axs[0][0].grid(True, which='both', linestyle='--', linewidth=0.5)
        axs[0][0].set_title('Present Class VCs Out Of Max Union VCs')
        for i in range(1, max_ways+1):
            if percent_cl_of_all_ext[i] == int(percent_cl_of_all_ext[i]):
                text = f"{int(percent_cl_of_all_ext[i])}"
            else:
                text = f"{round(percent_cl_of_all_ext[i], 2)}"
            axs[0][0].text(t_levels_ext[i], percent_cl_of_all_ext[i] + 3, text, ha='center', va='center')
    else:
        axs[0][0].set_axis_off()
        fails[0][0] = True

    # Class coverage out of max class ways
    success = safely_step_graph(axs[0][1], percent_cl_of_max_cl_ext, "Class Coverage", 'blue', xaxis=t_levels_ext)
    if success:
        axs[0][1].set_ylabel('Class Coverage (%)')
        axs[0][1].grid(True, which='both', linestyle='--', linewidth=0.5)
        axs[0][1].set_title('Present Class VCs Out Of Max Class VCs')
        for i in range(1, max_ways+1):
            if percent_cl_of_max_cl_ext[i] == int(percent_cl_of_max_cl_ext[i]):
                text = f"{int(percent_cl_of_max_cl_ext[i])}"
            else:
                text = f"{round(percent_cl_of_max_cl_ext[i], 2)}"
            axs[0][1].text(t_levels_ext[i], percent_cl_of_max_cl_ext[i] + 3, text, ha='center', va='center')
    else:
        axs[0][1].set_axis_off()
        fails[0][1] = True

    # Nonclass coverage out of max all ways
    success = safely_step_graph(axs[1][0], percent_nc_of_all_ext, "Nonclass Coverage", 'red', xaxis=t_levels_ext)
    if success:
        axs[1][0].set_ylabel('Nonclass Coverage (%)')
        axs[1][0].grid(True, which='both', linestyle='--', linewidth=0.5)
        axs[1][0].set_title('Present Nonclass VCs Out Of Max Union VCs')
        for i in range(1, max_ways+1):
            if percent_nc_of_all_ext[i] == int(percent_nc_of_all_ext[i]):
                text = f"{int(percent_nc_of_all_ext[i])}"
            else:
                text = f"{round(percent_nc_of_all_ext[i], 2)}"
            axs[1][0].text(t_levels_ext[i], percent_nc_of_all_ext[i] + 3, text, ha='center', va='center')
    else:
        axs[1][0].set_axis_off()
        fails[1][0] = True

    # Nonclass coverage out of max nonclass ways
    success = safely_step_graph(axs[1][1], percent_nc_of_max_nc_ext, "Nonclass Coverage", 'red', xaxis=t_levels_ext)
    if success:
        axs[1][1].set_ylabel('Nonclass Coverage (%)')
        axs[1][1].grid(True, which='both', linestyle='--', linewidth=0.5)
        axs[1][1].set_title('Present Nonclass VCs Out Of Max Nonclass VCs')
        for i in range(1, max_ways+1):
            if percent_nc_of_max_nc_ext[i] == int(percent_nc_of_max_nc_ext[i]):
                text = f"{int(percent_nc_of_max_nc_ext[i])}"
            else:
                text = f"{round(percent_nc_of_max_nc_ext[i], 2)}"
            axs[1][1].text(t_levels_ext[i], percent_nc_of_max_nc_ext[i] + 3, text, ha='center', va='center')
    else:
        axs[1][1].set_axis_off()
        fails[1][1] = True

    # Union coverage
    success = safely_step_graph(axs[2][0], percent_union_ext, "Union Coverage", 'purple', xaxis=t_levels_ext)
    if success:
        axs[2][0].set_ylabel('Union Coverage (%)')
        axs[2][0].grid(True, which='both', linestyle='--', linewidth=0.5)
        axs[2][0].set_title('Present Class + Nonclass VCs Out Of Max Union VCs')
        for i in range(1, max_ways+1):
            if percent_union_ext[i] == int(percent_union_ext[i]):
                text = f"{int(percent_union_ext[i])}"
            else:
                text = f"{round(percent_union_ext[i], 2)}"
            axs[2][0].text(t_levels_ext[i], percent_union_ext[i] + 3, text, ha='center', va='center')
    else:
        axs[2][0].set_axis_off()
        fails[2][0] = True
    axs[2][1].set_axis_off()

    for i in range(3):
        for j in range(2):
            if fails[i][j]:
                continue
            axs[i][j].legend(loc='best')
            axs[i][j].set_xlim(0.5, max_ways+0.5)
            axs[i][j].set_ylim(0, 110)
            axs[i][j].set_xlabel('T-way')
            axs[i][j].set_xticks(x_ticks)
            axs[i][j].set_yticks(y_ticks)
            axs[i][j].margins(x=0.1)

    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff
    dir_name = f"{output}\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    os.makedirs(dir_name, exist_ok=True)
    file_name = os.path.join(dir_name, "tway_coverage_graphs.png")
    plt.savefig(file_name, dpi=300) # bbox_inches='tight'
    plt.close(fig)

def run_data(context: CFDContext) -> None:

    """
    Main function to run the data analysis for distinguishing combinations.
    It initializes the CombinationCounter for class and nonclass data,
    counts the combinations, finds common entries, and discovers distinguishing combinations.
    It also generates output statements for unique and distinguishing combinations.
    Finally, it generates graphs and missing value combinations if not skipped.
    """

    class_file_data = context.class_file_data
    nonclass_file_data = context.nonclass_file_data
    ncc = context.ncc
    max_ways = context.max_t_ways
    gen_mvcs = context.gen_mvcs
    logs = context.logs
    silent = context.silenced or context.silenced_ts
 
    print_timestamp_message(context, f"Discovering common entries")
    common_entries = find_common_entries(context)
    context.common_entries = common_entries
    
    class_file_data = context.class_file_data
    nonclass_file_data = context.nonclass_file_data

    print_timestamp_message(context, "Beginning class calculations")
    counter_class = CombinationCounter(class_file_data, "Class")
    counter_class.count_combinations(context)
    combination_counts_class = counter_class.get_combination_counts()
    context.combination_counts_class = combination_counts_class

    print_timestamp_message(context, "Beginning nonclass calculations")
    counter_nonclass = CombinationCounter(nonclass_file_data, "Nonclass")
    counter_nonclass.count_combinations(context)
    combination_counts_nonclass = counter_nonclass.get_combination_counts()
    context.combination_counts_nonclass = combination_counts_nonclass

    print_timestamp_message(context, "Discovering distinguishing combinations")
    distin_tway_combos: dict[str, tuple[list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]], 
        list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]]]] = {}

    uniq_inter_tway: dict[str, tuple[tuple[int, int], list[int]]] = {}

    for t in range(1, 7):
        distin_lower_cl_list: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]] = []
        distin_lower_nc_list: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]] = []
        if context.filter:
            for i in range(1, t):
                distin_lower_cl_list += distin_tway_combos[f'{i}-way'][0]
                distin_lower_nc_list += distin_tway_combos[f'{i}-way'][1]

        total_iters = len(combination_counts_class[f'{t}-way']) + len(combination_counts_nonclass[f'{t}-way'])

        def calc_it(hide_bar: bool, timeout: bool) -> bool:
            start_time = time.time() if timeout else 0
            pbar = tq(total=total_iters, desc=f"{t}-way Distinguishing Calculations", disable=hide_bar)
            success, t_way_combos_cl, n_uniq_cl, n_inter_cl = find_distinguishing_combos(
                context,
                combination_counts_class[f'{t}-way'],
                combination_counts_nonclass[f'{t}-way'],
                distin_lower_cl_list,
                True,
                t,
                pbar,
                start_time
            )
            if not success:
                return False
            success, t_way_combos_nc, n_uniq_nc, n_inter_nc = find_distinguishing_combos(
                context,
                combination_counts_nonclass[f'{t}-way'],
                combination_counts_class[f'{t}-way'],
                distin_lower_nc_list,
                False,
                t,
                pbar,
                start_time
            )
            if not success:
                return False
            distin_tway_combos[f'{t}-way'] = (t_way_combos_cl, t_way_combos_nc)
            uniq_inter_tway[f'{t}-way'] = (((n_uniq_cl, n_uniq_nc), [n_inter_cl, n_inter_nc]))
            return True
        if logs and not silent:
            if not calc_it(True, True):
                calc_it(False, False)
        else:
            calc_it(True, False)

    context.distin_tway_combos = distin_tway_combos
    distinguishing_tway_combos = context.distin_tway_combos

    print_timestamp_message(context, "Calculating class value frequencies")
    val_freq_class, distinct_values_class = counter_class.get_value_frequencies_and_distinct_values()

    print_timestamp_message(context, "Calculating nonclass value frequencies")
    val_freq_nonclass, distinct_values_nonclass = counter_nonclass.get_value_frequencies_and_distinct_values()

    print_timestamp_message(context, "Calculating unique values")
    unique_to_class: list[list[ValueString]] = []
    for key in distinct_values_class.keys():
        if key in distinct_values_nonclass:
            difference_set = distinct_values_class[key] - \
                distinct_values_nonclass[key]
        else:
            difference_set = distinct_values_class[key]
        unique_to_class.append(list(difference_set))

    num_uniq_vals_class = sum(len(lst) for lst in unique_to_class)

    unique_to_nonclass: list[list[ValueString]] = []
    for key in distinct_values_nonclass.keys():
        if key in distinct_values_class:
            difference_set = distinct_values_nonclass[key] - \
                distinct_values_class[key]
        else:
            difference_set = distinct_values_nonclass[key]
        unique_to_nonclass.append(list(difference_set))

    num_uniq_vals_nonclass = sum(len(lst) for lst in unique_to_nonclass)

    print_timestamp_message(context, "Counting distinguishing combinations")
    sum_distin_ways: dict[str, int] = {f'{t}-way': 0 for t in range(1, 7)}
    total_distinguishing = 0
    for t in range(1, 7):
        if t > max_ways:
            break
        num_class = len(distinguishing_tway_combos[f"{t}-way"][0])
        num_nonclass = len(distinguishing_tway_combos[f"{t}-way"][1])
        sum_tway = num_class + num_nonclass
        sum_distin_ways[f"{t}-way"] = sum_tway
        total_distinguishing += sum_tway

    print_timestamp_message(context, "Determining class entries with distinguishing combinations")
    occur_class = count_entries_with_distinguishing_combos(context, class_file_data, distin_tway_combos, 0)

    print_timestamp_message(context, "Determining nonclass entries with distinguishing combinations")
    occur_nonclass = count_entries_with_distinguishing_combos(context, nonclass_file_data, distin_tway_combos, 1)

    # Count entries with distinguishing combinations
    occur_tway: dict[str, int] = {}
    for t in range(1, 7):
        key = f"{t}-way"
        occur_tway[key] = occur_class[t-1] + occur_nonclass[t-1]

    occur_distinguishing = sum(occur_class) + sum(occur_nonclass)

    max_class_1way = sum(len(values) for values in distinct_values_class.values())
    max_nonclass_1way = sum(len(values) for values in distinct_values_nonclass.values())
    max_all_1way = sum(len(distinct_values_class.get(key, set()).union(distinct_values_nonclass.get(
        key, set()))) for key in set(distinct_values_class) | set(distinct_values_nonclass))

    max_class_tway_values: list[int] = []
    max_class_tway_combos: list[dict[tuple[ValueIndex, ...], list[tuple[ValueString, ...]]]] = []
    max_nonclass_tway_values: list[int] = []
    max_nonclass_tway_combos: list[dict[tuple[ValueIndex, ...], list[tuple[ValueString, ...]]]] = []
    max_all_tway_values: list[int] = []
    max_all_tway_combos: list[dict[tuple[ValueIndex, ...], list[tuple[ValueString, ...]]]] = []
    max_class_tway_values.append(max_class_1way)
    max_nonclass_tway_values.append(max_nonclass_1way)
    max_all_tway_values.append(max_all_1way)

    max_ways = context.max_t_ways

    print_timestamp_message(context, f"Calculating maximum possible interactions")
    distinct_values_union: dict[ValueIndex, set[ValueString]] = {}

    for key in set(distinct_values_class.keys()).union(set(distinct_values_nonclass.keys())):
        distinct_values_union[key] = set(distinct_values_class.get(key, set())).union(
            distinct_values_nonclass.get(key, set()))

    def do_max_calc(t: int, hide_bar: bool, total_iters: int, start: float) -> bool:
        pbar = tq(total=total_iters, desc=f"{t}-way Maximum Interactions", disable=hide_bar)

        class_result = calculate_max_possible_t_interactions(context, distinct_values_class, t, start, pbar)
        if not class_result[0]:
            return False
        nonclass_result = calculate_max_possible_t_interactions(context, distinct_values_nonclass, t, start, pbar)
        if not nonclass_result[0]:
            return False
        all_result = calculate_max_possible_t_interactions(context, distinct_values_union, t, start, pbar)
        if not all_result[0]:
            return False

        max_class_tway_values.append(class_result[1])
        max_class_tway_combos.append(class_result[2])
        max_nonclass_tway_values.append(nonclass_result[1])
        max_nonclass_tway_combos.append(nonclass_result[2])
        max_all_tway_values.append(all_result[1])
        max_all_tway_combos.append(all_result[2])
        return True

    for t in range(2, 7):
        total_iters = len(list(combinations(distinct_values_class, t))) + \
            len(list(combinations(distinct_values_nonclass, t))) + len(list(combinations(distinct_values_union, t)))
        if logs and not silent:
            start_time = time.time()
            if not do_max_calc(t, True, total_iters, start_time):
                do_max_calc(t, False, total_iters, 0)
        else:
            do_max_calc(t, True, total_iters, 0)

    print_timestamp_message(context, "Counting common combinations")
    common_combinations = count_common_combinations(context, combination_counts_class, combination_counts_nonclass)

    tway_lens:dict[str, tuple[int, int]] = {}

    for t in range(1, 7):
        key = f"{t}-way"
        tway_lens[key] = (len(combination_counts_class[key]), len(combination_counts_nonclass[key]))

    print_timestamp_message(context, f"Generating DVC statements")
    for t in range(1, max_ways+1):
        generate_output_statements(
            context,
            distinguishing_tway_combos[f'{t}-way'][0],
            distinguishing_tway_combos[f'{t}-way'][1],
            t
        )

    missing_tway_combos: dict[str, tuple[list[tuple[tuple[str, ...], list[int]]],
                                         list[tuple[tuple[str, ...], list[int]]],
                                         list[tuple[tuple[str, ...], list[int]]]]] = {}

    print_timestamp_message(context, f"Beginning missing value combinations")
    for t in range(2, 7):
        key = f"{t}-way"
        results = find_missing_combos(context, max_all_tway_combos[t-2], t, \
            max_class_tway_combos[t-2], max_nonclass_tway_combos[t-2])
        missing_tway_combos[key] = (results[0], results[1], results[2])

    context.missing_tway_combos = missing_tway_combos

    if gen_mvcs:
        print_timestamp_message(context, "Missing combinations counted")

    combined_combination_counts = merge_combination_counts(
        combination_counts_class, combination_counts_nonclass)

    distinguishing_combination_counts = filter_distinguishing(context, combined_combination_counts, {
        '1-way': distinguishing_tway_combos['1-way'][0] + distinguishing_tway_combos['1-way'][1],
        '2-way': distinguishing_tway_combos['2-way'][0] + distinguishing_tway_combos['2-way'][1],
        '3-way': distinguishing_tway_combos['3-way'][0] + distinguishing_tway_combos['3-way'][1],
        '4-way': distinguishing_tway_combos['4-way'][0] + distinguishing_tway_combos['4-way'][1],
        '5-way': distinguishing_tway_combos['5-way'][0] + distinguishing_tway_combos['5-way'][1],
        '6-way': distinguishing_tway_combos['6-way'][0] + distinguishing_tway_combos['6-way'][1]
    })

    ret = aggregate_counts_by_variable_distinguishing(
        context,
        distinguishing_combination_counts
    )

    distinguishing_counts: dict[str, list[int]] = {}
    for t in range(1, 7):
        distinguishing_counts[f'{t}-way'] = ret[t-1]

    print_timestamp_message(context, "Analyzing Combos")
    analyze_combos(context, combination_counts_class, combination_counts_nonclass)

    for t in range(1, max_ways+1):
        distinguishing_coverage_graph(context, t)

    context.avg_val_per_var = max_all_1way / ncc

    data = {
        "num_diff_values": max_all_1way,
        "num_intersect_vals": common_combinations['1-way'],
        "num_uniq_vals_class": num_uniq_vals_class,
        "num_uniq_vals_nonclass": num_uniq_vals_nonclass,
        "num_distinguishing": total_distinguishing,
        "occur_distinguishing": occur_distinguishing,

        "grid": [[max_all_tway_values[0], max_class_tway_values[0], max_nonclass_tway_values[0], tway_lens['1-way'][0], tway_lens['1-way'][1], common_combinations['1-way'], sum_distin_ways['1-way'], (sum_distin_ways['1-way'] / total_distinguishing) if total_distinguishing != 0 else 0, occur_tway['1-way'], (occur_tway['1-way'] / occur_distinguishing) if occur_distinguishing != 0 else 0],
                 [max_all_tway_values[1], max_class_tway_values[1], max_nonclass_tway_values[1], tway_lens['2-way'][0], tway_lens['2-way'][1], common_combinations['2-way'], sum_distin_ways['2-way'], (sum_distin_ways['2-way'] / total_distinguishing) if total_distinguishing != 0 else 0, occur_tway['2-way'], (occur_tway['2-way'] / occur_distinguishing) if occur_distinguishing != 0 else 0],
                 [max_all_tway_values[2], max_class_tway_values[2], max_nonclass_tway_values[2], tway_lens['3-way'][0], tway_lens['3-way'][1], common_combinations['3-way'], sum_distin_ways['3-way'], (sum_distin_ways['3-way'] / total_distinguishing) if total_distinguishing != 0 else 0, occur_tway['3-way'], (occur_tway['3-way'] / occur_distinguishing) if occur_distinguishing != 0 else 0],
                 [max_all_tway_values[3], max_class_tway_values[3], max_nonclass_tway_values[3], tway_lens['4-way'][0], tway_lens['4-way'][1], common_combinations['4-way'], sum_distin_ways['4-way'], (sum_distin_ways['4-way'] / total_distinguishing) if total_distinguishing != 0 else 0, occur_tway['4-way'], (occur_tway['4-way'] / occur_distinguishing) if occur_distinguishing != 0 else 0],
                 [max_all_tway_values[4], max_class_tway_values[4], max_nonclass_tway_values[4], tway_lens['5-way'][0], tway_lens['5-way'][1], common_combinations['5-way'], sum_distin_ways['5-way'], (sum_distin_ways['5-way'] / total_distinguishing) if total_distinguishing != 0 else 0, occur_tway['5-way'], (occur_tway['5-way'] / occur_distinguishing) if occur_distinguishing != 0 else 0],
                 [max_all_tway_values[5], max_class_tway_values[5], max_nonclass_tway_values[5], tway_lens['6-way'][0], tway_lens['6-way'][1], common_combinations['6-way'], sum_distin_ways['6-way'], (sum_distin_ways['6-way'] / total_distinguishing) if total_distinguishing != 0 else 0, occur_tway['6-way'], (occur_tway['6-way'] / occur_distinguishing) if occur_distinguishing != 0 else 0]],

        "count1": distinguishing_counts['1-way'],
        "count2": distinguishing_counts['2-way'],
        "count3": distinguishing_counts['3-way'],
        "count4": distinguishing_counts['4-way'],
        "count5": distinguishing_counts['5-way'],
        "count6": distinguishing_counts['6-way'],

        "val_freq_class": val_freq_class,
        "val_freq_nonclass": val_freq_nonclass,
        "common_entries": common_entries,

        "occur_distinguishing_list":
           [[uniq_inter_tway['1-way'][0][0], uniq_inter_tway['1-way'][0][1], sum(uniq_inter_tway['1-way'][1])],
            [uniq_inter_tway['2-way'][0][0], uniq_inter_tway['2-way'][0][1], sum(uniq_inter_tway['2-way'][1])],
            [uniq_inter_tway['3-way'][0][0], uniq_inter_tway['3-way'][0][1], sum(uniq_inter_tway['3-way'][1])],
            [uniq_inter_tway['4-way'][0][0], uniq_inter_tway['4-way'][0][1], sum(uniq_inter_tway['4-way'][1])],
            [uniq_inter_tway['5-way'][0][0], uniq_inter_tway['5-way'][0][1], sum(uniq_inter_tway['5-way'][1])],
            [uniq_inter_tway['6-way'][0][0], uniq_inter_tway['6-way'][0][1], sum(uniq_inter_tway['6-way'][1])]]
    }

    context.data = data
    print_timestamp_message(context, "Calculations complete")

if __name__ == "__main__":
    context = parse_args()
    main(context)
