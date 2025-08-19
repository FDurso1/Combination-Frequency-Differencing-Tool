'''
Combination Frequency Differencing (CFD) is a technique used to identify patterns that distinguish one group of 
data from another by analyzing how combinations of variable values (ex, color + shape + size) appear across the groups.
Rather than looking at variables individually, CFD examines all t-way interactions (es, 2-way, 3-way, etc.) to find 
which combinations occur distinguishingly more frequently in one file than in the other, making them Distinguishing 
Value Combinations (DVCs).

Please read through the Command Line Guide for full usage capabilities and instructions.

Version [major update] . [bug fix] . [minor update / new feature]
Version 1.0.2
Last Updated: 8/19/2025
Author: Francis Durso
'''

import shutil
import subprocess
import importlib
import sys
import os
import argparse
from datetime import datetime
import time
from itertools import combinations, product
from collections import Counter, defaultdict
import re
import csv
from typing import cast, TypeAlias

# Type aliases for more readable code, used in most places
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
        # self.data contains many of the calculated results
        self.data: dict[str, int | list[list[int]] | list[dict[str, int]]] | dict[str, list[list[int]]] = {}
        self.distinguishability_cutoff: float = 0.0 # User chosen distinguishability cutoff
        self.max_t_ways: int = 0 # User chosen flag for how many t-ways should be calculated, default is 3.
        self.verbose: bool = False # User chosen flag to make the outputs use variable names if present
        self.logs: bool = False # User chosen flag to log program execution
        self.gen_graphs: bool = False # User chosen flag to generate graphical outputs
        self.gen_mvcs: bool = False # User chosen flag to generate missing value combinations
        self.overwrite: bool = False # User chosen flag to auto overwrite existing files
        self.remove_dups: bool = False # User chosen flag to auto remove duplicate rows from data
        self.complete_rows_only: bool = False # User chosen flag to remove all incomplete data before processing
        self.silenced: bool = False # User chosen flag to silence all non-prompting terminal outputs
        self.silenced_info: bool = False # Variation of above flag to only silence info statements
        self.silenced_ts: bool = False # Variation of above flag to only silence timestamp statements
        self.output_path: str = "" # User chosen flag to specify an output folder for results
        self.auto_drop: bool = False # User specified flag to always drop recommended columns
        self.delimiter: str = "" # User specified delimiter for the CSV files, default is a comma.
        self.bin_style: str = "" # User specified flag for whether they should be prompted to bin continuous data
        self.filter: bool = False # User specified flag to filter out lower t-level DVCs from higher ones.
        self.start_time: datetime = datetime.now() # Start time of the operation
        self.class_file_duplicates: list[dict[str, str]] = [] # List of duplicate values in the class file
        self.nonclass_file_duplicates: list[dict[str, str]] = [] # List of duplicate values in the nonclass file
        self.variable_names: list[str] = [] # List of variable names if present, otherwise Var 1, Var 2, etc
        self.max_name_length: int = 0 # Length of the longest variable name (for spacing)
        self.ncc: int = 0 # Number of columns / variables
        self.nrc: int = 0 # Number of rows in the class file
        self.nrn: int = 0 # Number of rows in the nonclass file
        self.class_file_data: list[list[ValueString]] = [] # The data from the class file
        self.nonclass_file_data: list[list[ValueString]] = [] # The data from the nonclass file
        self.has_header: bool = False # Is a header present in either file
        self.class_file_path: str = "" # Class file path
        self.nonclass_file_path: str = "" # Nonclass file path
        self.class_file_name: str = "" # Class file name
        self.nonclass_file_name: str = "" # Nonclass file name
        self.common_entries: list[tuple[tuple[ValueString, ...], dict[str, int]]] = [] # Entries present in both classes
        self.avg_val_per_var: float = 0.0 # The average number of values each variable holds
        self.csv_print_1way: list[tuple[list[str], str]] = [] # Hold the DVC CSV file output data for 1-way
        self.csv_print_2way: list[tuple[list[str], str]] = [] # For 2-way
        self.csv_print_3way: list[tuple[list[str], str]] = [] # For 3-way
        self.csv_print_4way: list[tuple[list[str], str]] = [] # For 4-way
        self.csv_print_5way: list[tuple[list[str], str]] = [] # For 5-way
        self.csv_print_6way: list[tuple[list[str], str]] = [] # For 6-way
        # Dictionary to hold combination counts for class file
        self.combination_counts_class: dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency]] = {}
        # Dictionary to hold combination counts for nonclass file
        self.combination_counts_nonclass: dict[str, dict[tuple[ValueCombo_Tuple_index_str, ...], ComboFrequency]] = {}
        self.distin_tway_combos: dict[str, tuple[list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]],
            list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]]]] = {}
        # Contain missing value combinations
        self.missing_tway_combos: dict[str, tuple[list[tuple[tuple[str, ...], list[int]]], 
                                                  list[tuple[tuple[str, ...], list[int]]]]] = {} 
        self.num_warnings: int = 0 # Number of warnings the program produces (to display if logs are enabled)
        self.column_names_dropped: list[str] = [] # Names of all columns dropped if --drop flag was enabled
        # Maps feature names to their original number of unique values and new bin ranges
        self.feature_bin_ranges: list[tuple[str, int, list[tuple[float, float]]]] = [] 

def print_warning_message(context: CFDContext, message: str, is_error: bool=False, do_not_write=False) -> None:

    """
    Prints a warning message to the console and logs it to the logs file if logs are enabled.
    If the message is an error, instead print to stderr, write it to logs if logs are enabled, then exit.
    """

    warn_type = "WARNING"
    if is_error:
        warn_type = "ERROR"

        # Convert message to uppercase except for the parts inside quotes (to preserve case-specific flag instructions)
        def to_upper_except_quotes(msg: str):
            result = []
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

    if context.logs and not do_not_write:
        now = datetime.now()
        formatted_time = now.strftime("%H:%M:%S")
        class_file_name = context.class_file_name
        nonclass_file_name = context.nonclass_file_name
        distinguishability_cutoff = context.distinguishability_cutoff
        sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
        os.makedirs(sub_dir_name, exist_ok=True)
        new_file_name = f"Logs.txt"
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

    if not (context.silenced or context.silenced_info) or print_anyway: 
        # print_anyway is used for printing info messages preceeding user input
        termcolor.cprint(f"Info: {message}.", "cyan")

    if context.logs:
        now = datetime.now()
        formatted_time = now.strftime("%H:%M:%S")
        class_file_name = context.class_file_name
        nonclass_file_name = context.nonclass_file_name
        distinguishability_cutoff = context.distinguishability_cutoff
        sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
        os.makedirs(sub_dir_name, exist_ok=True)
        new_file_name = f"Logs.txt"
        file_path = os.path.join(sub_dir_name, new_file_name)
        with open(file_path, "a") as file:
            file.write(f"Info: {message} - {formatted_time}\n")
            file.close()

def install_and_import(context: CFDContext, pkg_name: str) -> None:

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
                print_warning_message(context, f"Was unable to install '{pkg_name}' automatically.\n\
Please attempt to manually install this package and then rerun", True)
        print_info_message(context, f"Installed {pkg_name}")
        install_and_import(context, pkg_name) # Retry after install

# Non-standard library imports
import pandas as pd
import matplotlib.pyplot as plt
import matplotlib.axes as mpl_axes
import numpy as np
from matplotlib_venn import venn2
from matplotlib_venn._common import VennDiagram as Venn
import termcolor
from tqdm import tqdm as tq
import kmeans1d


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

    sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
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
        if all(value == 0 for value in [class_VIs, nonclass_VIs, intersect_VIs]):
            row[1].text(0.5, 0.5, "No Applicable Data", ha='center', va='center', fontsize=12)
            vd = None
        else:
            vd = venn2(subsets=(class_VIs, nonclass_VIs, intersect_VIs), set_colors=('#305CDE', 'red'), 
                set_labels=('', ''), ax=row[1])

        if all(value == 0 for value in [distinguishing_class_VIs, distinguishing_nonclass_VIs, 
                distinguishing_intersect_VIs]):
            row[3].text(0.5, 0.5, "No Applicable Data", ha='center', va='center', fontsize=12)
            nvd = None
        else:
            nvd = venn2(subsets=(distinguishing_class_VIs, distinguishing_nonclass_VIs, distinguishing_intersect_VIs),
                set_colors=('#305CDE', 'red'), set_labels=('', ''), ax=row[3])

        # Add "Class" and "Nonclass" labels if applicable
        def label_by_id(label: str, ID: str, diagram: Venn|None):
            if diagram:
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
    filename = os.path.join(graphs_dir, "venn_diagram.png")
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

    sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    graphs_dir = os.path.join(sub_dir_name, "Graphs", "Pie Graphs")
    os.makedirs(graphs_dir, exist_ok=True)

    pie_comp_list = [variable_names.index(name) for name in variable_names]

    val_freq_class = cast(list[dict[str, ComboFrequency]], data['val_freq_class'])
    val_freq_nonclass = cast(list[dict[str, ComboFrequency]], data['val_freq_nonclass'])

    for idx in tq(pie_comp_list, desc='Pie Progress', disable=(not logs or silent)):
        var_name = variable_names[idx] # .replace(" ", "_")

        if not any(val_freq_class[idx].values()) or not any(val_freq_nonclass[idx].values()):
            print_warning_message(context, f"No pie chart data available for {var_name}")
            continue

        unique_labels_class = list(val_freq_class[idx].keys())
        unique_labels_nonclass = list(val_freq_nonclass[idx].keys())
        unique_labels_class.sort()
        unique_labels_nonclass.sort() # Should ensure that values appear in the same (general) order in the pie charts
        all_unique_labels = list(set(unique_labels_class + unique_labels_nonclass))

        colors_map = plt.colormaps['tab20']
        colors = colors_map(np.linspace(0, 1, len(all_unique_labels)))
        color_map = {label: colors[i] for i, label in enumerate(all_unique_labels)}
        # Ensures each pie slice is the same color for the same value between pie charts

        try:
            fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 6))
            ax1 = cast(mpl_axes.Axes, ax1)
            ax2 = cast(mpl_axes.Axes, ax2)

            # Class pie chart
            ax1.pie(
                list(val_freq_class[idx].values()),
                labels=unique_labels_class,
                autopct='%1.1f%%',
                startangle=140,
                colors=[color_map[v] for v in unique_labels_class],
            )
            ax1.axis('equal')
            ax1.set_title(f"{var_name} - Class File")

            # Nonclass pie chart
            ax2.pie(
                list(val_freq_nonclass[idx].values()),
                labels=unique_labels_nonclass,
                autopct='%1.1f%%',
                startangle=140,
                colors=[color_map[v] for v in unique_labels_nonclass],
            )
            ax2.axis('equal')
            ax2.set_title(f"{var_name} - Nonclass File")

            save_path = os.path.join(graphs_dir, f"{var_name}.png")
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            plt.close(fig)

        except ValueError as ex:
            termcolor.cprint(f"Value error occurred while pie chart plotting for {var_name}.\nException: {ex}",
                "light_red", file=sys.stderr)

def get_correct_bar_CSV_header(t: int) -> str:

    """
    Returns the correct header for the bar graph's CSV file based on the t-way interaction level.
    """

    ways_str = ",".join(f"{x}-way" for x in range(1, t+1))
    ret_str = f"Name,{ways_str}\n"
    return ret_str

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

    sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    graphs_dir = os.path.join(sub_dir_name, "Graphs")
    os.makedirs(graphs_dir, exist_ok=True)

    csv_file_name = f"feature_DVC_bar_graph_{class_file_name}_{nonclass_file_name}_{distinguishability_cutoff}.csv"
    csv_file_path = os.path.join(graphs_dir, csv_file_name)
    with open(csv_file_path, 'w') as csv_file:
        csv_file.write(get_correct_bar_CSV_header(max_ways))
        for i in range(len(variable_names)):
            counts = [cast(list[dict[str, int]], data[f'count{j+1}'])[i] for j in range(max_ways)]
            csv_file.write(f"{variable_names[i]},{','.join(map(str, counts))}\n")

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

def get_the_right_MVC_files(context: CFDContext, t: int) -> tuple[list[tuple[tuple[str, ...], list[int]]],
                                                                  list[tuple[tuple[str, ...], list[int]]]]:

    """
    Returns the appropriate missing value combinations (MVCs) file for the specified t-way interaction.
    """

    missing_tway_combos = context.missing_tway_combos
    return missing_tway_combos[f'{t}-way'][0], missing_tway_combos[f'{t}-way'][1]

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

    if max_ways == 1:
        # There are no MVCs for only 1-way interactions
        print_warning_message(context, 
            "No missing value combinations can be generated for 1-way interactions")
        return

    sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    MVCs_dir = os.path.join(sub_dir_name, "MVCs")
    os.makedirs(MVCs_dir, exist_ok=True)

    for r in range(2,max_ways+1):
        new_file_name = f"{r}-way-MVCs.txt"
        file_path = os.path.join(MVCs_dir, new_file_name)

        with open(file_path, "w") as file:
            MVC_class_file, MVC_nonclass_file = get_the_right_MVC_files(context, r)
            for elem in MVC_class_file:
                file.write(f"{elem[0]} values for {[variable_names[i] for i in elem[1]]} \
is not present in the class file\n")
            for elem in MVC_nonclass_file:
                file.write(f"{elem[0]} values for {[variable_names[i] for i in elem[1]]} \
is not present in the nonclass file\n")
            file.close()
 
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

    sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    dvcs_dir = os.path.join(sub_dir_name, "DVCs")
    os.makedirs(dvcs_dir, exist_ok=True)

    def write_dvcs(hide_bar: bool, timeout: bool, t: int) -> bool:
        st = time.time()
        entries_list, header_str = get_the_right_file(context, t)
        new_file_name = f"{t}-way_DVCs.csv"
        file_path = os.path.join(dvcs_dir, new_file_name)

        with open(file_path, "w") as file:
            file.write(header_str)
            for entry in tq(entries_list, desc=f"{t}-way DVCs", disable=hide_bar):
                file.write(f"{entry}\n")
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
    avg_val_per_var = context.avg_val_per_var
    variable_names = context.variable_names
    max_ways = context.max_t_ways
    auto_dropped = context.auto_drop
    dropped_columns = context.column_names_dropped
    auto_remove_dups = context.remove_dups
    feature_bins = context.feature_bin_ranges
    filter = context.filter

    grid = cast(list[list[int]], data['grid'])
    common_entries = cast(list[tuple[tuple[str], dict[str,int]]], data['common_entries'])

    sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    os.makedirs(sub_dir_name, exist_ok=True)
    new_file_name = f"Info.txt"
    file_path = os.path.join(sub_dir_name, new_file_name)

    disclaimer = """
Disclaimer: Research Prototype Tool

This tool is provided as a research prototype and is intended for experimental and informational purposes only. 
Users are advised that the tool may produce inaccurate or incomplete information and may contain unknown bugs or \
errors.
The results generated by the tool should be treated with caution and should not be relied upon as the sole basis \
for decision-making in critical settings.
Users are strongly encouraged to validate the tool's output using reliable and established methods before making \
any critical decisions.
The developers and providers of this tool shall not be held responsible for any consequences arising from the \
use of its results without proper validation or for any actions taken based on the tool's output.

By using this tool, you acknowledge and accept the inherent limitations and uncertainties associated with \
research prototypes and agree to exercise due diligence in verifying its results prior to implementation \
in critical or important contexts.
"""

    today_date = datetime.now().strftime('%Y-%m-%d')
    var_names = ', '.join(str(name) for name in variable_names)

    with open(file_path, "w") as file:
        file.write(disclaimer)
        file.write('\n')
        file.write(f"Today's date: {today_date}\n")
        file.write(f"t-level specified: {max_ways}\n")
        file.write(f"Class file: {class_file_name}\n")
        file.write(f"Nonclass file: {nonclass_file_name}\n")
        file.write(f"Number of class rows: {nrc}\n")
        file.write(f"Number of nonclass rows: {nrn}\n\n")

        if auto_dropped:
            if len(dropped_columns) == 0:
                file.write(f"No columns were automatically dropped\n\n")
                file.write(f"Number of variables: {ncc}\n")
            else:
                file.write(f"{len(dropped_columns)} columns were automatically dropped:")
                cols = '\t'.join(dropped_columns)
                file.write(f"{cols}\n\n")
                file.write(f"Number of variables remaining: {ncc}\n")
        else:
            file.write(f"Number of variables: {ncc}\n")
        if has_header:
            file.write(var_names + '\n')
        file.write("\n")
        if feature_bins != []:
            plural = "features were" if len(feature_bins) > 1 else "feature was"
            file.write(f"{len(feature_bins)} {plural} binned:\n")
            padding = [max(len(f[0]) for f in feature_bins), max(len(str(f[1])) for f in feature_bins), 
max(len(str(len(f[2]))) for f in feature_bins)]
            for tup in feature_bins:
                ranges = ', '.join(str(item) for item in tup[2])
                file.write(f"{tup[0]:<{padding[0]}} ({tup[1]:<{padding[1]}} values down to \
{str(len(tup[2])):<{padding[2]}}): {ranges}\n")
        else:
            file.write("No features were binned\n")
        binned = "After binning, there" if feature_bins != [] else "There"
        file.write(f"\n{binned} are {data['num_diff_values']} different values taken on by these variables, "
f"with an average of {avg_val_per_var:.3f} values per variable.\n")
        file.write(f"{data['num_intersect_vals']} of these values are present in both files.\n")
        file.write(f"{data['num_uniq_vals_class']} are only present in the class file.\n")
        file.write(f"{data['num_uniq_vals_nonclass']} are only present in the nonclass file.\n\n")

        len_common = len(common_entries)
        if len_common > 0:
            file.write(f"{len_common} entries appeared in both files:\n")
            for entry in common_entries:
                entry_values, counts = entry[0], entry[1]
                class_count = counts['class_count']
                nonclass_count = counts['nonclass_count']
                file.write(
                    f"Entry: {entry_values}:\nClass Count: {class_count}, Nonclass Count: {nonclass_count}\n\n")
        else:
            file.write("No entries appeared in both files.\n\n")

        if class_file_duplicates != []:
            file.write(f"{len(class_file_duplicates)} duplicate rows were detected in the class file.\n")
            with open(os.path.join(sub_dir_name, f"{class_file_name}_duplicates.csv"), "w") as class_dup_file:
                class_dup_file.write(",".join(str(value) for value in context.variable_names) + "\n")
                for row in class_file_duplicates:
                    class_dup_file.write(",".join(value for value in row.values()) + "\n")

        if nonclass_file_duplicates != []:
            file.write(f"{len(nonclass_file_duplicates)} duplicate rows were detected in the nonclass file.\n")
            with open(os.path.join(sub_dir_name, f"{nonclass_file_name}_duplicates.csv"), "w") as nonclass_dup_file:
                nonclass_dup_file.write(",".join(str(value) for value in context.variable_names) + "\n")
                for row in nonclass_file_duplicates:
                    nonclass_dup_file.write(",".join(str(value) for value in row.values()) + "\n")

        num_dups = len(class_file_duplicates) + len(nonclass_file_duplicates)
        if auto_remove_dups and num_dups > 0:
            plural = "rows were" if num_dups > 1 else "row was"
            file.write(f"The duplicate {plural} removed before processing\n")
        if filter:
            file.write("\nThe filter was enabled. T-way DVCs which contain a lower level t-way DVC are \
not themselves also considered DVCs.\n\n")
        else:
            file.write("\nThe filter was not enabled. T-way DVCs which contain a lower t-level DVC still qualify.\n\n")        

        for t in range(max_ways):
            file.write(f"At t-level {t+1} there are:\n")
            file.write(f" * Maximum Value Interactions:             {grid[t][0]}\n")
            file.write(f" * Maximum Class Value Interactions:       {grid[t][1]}\n")
            file.write(f" * Maximum Nonclass Value Interactions:    {grid[t][2]}\n")
            file.write(f" * Present Class Value Interactions:       {grid[t][3]}\n")
            file.write(f" * Present Nonclass Value Interactions:    {grid[t][4]}\n")
            file.write(f" * Value Combinations Present in Both:     {grid[t][5]}\n")
            file.write(f" * Distinguishing Value Combinations:      {grid[t][6]}\n")
            file.write(f" * Percent of All DVCs:                    {grid[t][7]}\n")
            file.write(f" * Number of DVC Occurrences:              {grid[t][8]}\n")
            file.write(f" * Percent of All DVC Occurrences:         {grid[t][9]}\n")
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

def sanitize_name(name: str, replacement: str='_', file: str='') -> str:

    """
    Replaces or removes characters unsafe for filenames / variable names
    Also collapses repeated separators and trims leading/trailing separators.
    """

    # Replace unsafe characters with the replacement character
    name = re.sub(r'[<\'>\f:"\t,\b;&/\\|\r?*\n]', replacement, name)
    # Replace non-ascii characters with the replacement character
    name = re.sub(r'[^\x00-\x7F]+', replacement, name)

    # Collapse multiple replacement characters (e.g., "__" -> "_")
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
        print("You must at a minimum provide a path to your [class_file], your [nonclass_file], \
and your [distinguishing cutoff].\n")
        print("For more information, please refer to the CFD Command Line Guide manual or call --help\n")
        sys.exit(1)

def parse_args() -> CFDContext:

    """
    Parse all command line arguments and create the Context object which will store them, among other data
    """

    parser = CustomArgumentParser(
        description="Combination Frequency Differencing Tool (CFD) Command Line Interface (CLI) Dev Version 1.0.1",
        epilog="For more information, please refer to the CFD Command Line Guide.\n"
    )
    parser.add_argument(
        "class_file",
        help="Path to the class file (CSV format)")
    parser.add_argument(
        "nonclass_file",
        help="Path to the nonclass file (CSV format)")
    parser.add_argument(
        "distinguishability_cutoff",
        type=float,
        help="Threshold multiplier for distinguishing combinations")
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
        help="Generate missing value combinations (MVCs) for each t-way interaction level and save them to text files",
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
        "-t", "--t", "--tway", "--max_t_ways", "--max", "--max_t", "--max_ways",
        type=int, 
        default=3,
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
        default='_FALSE',
        const='all',
        help="Silence all program output to the terminal except for errors and user prompts.\n\
Alternatively, specify \'--silent info\' or \'--silent ts\' to silence only info or timestamp statements to terminal respectively",
        dest='silent'
    )
    parser.add_argument(
        "--drop", "--autodrop", "--recdrop",
        action="store_true",
        default=False,
        help="Automatically drop columns from the class and nonclass files if the tool recommends it; \
original files will not be affected",
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
        "--bin",
        nargs='?',
        default='_FALSE',
        const='manual',
        help="When a feature is determined to be continuous, gain the ability to bin it before proceeding",
        dest='bin'
    )
    parser.add_argument(
        '-out', '--output',
        nargs='?',
        const='output',
        default='output',
        help='Specify an output folder for results. Default: "output"',
        dest='output'
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
    context.silenced = True if (args.silent).lower() == 'all' else False
    context.silenced_info = True if (args.silent).lower() == 'info' else False
    context.silenced_ts = True if (args.silent).lower() == 'ts' else False
    context.auto_drop = args.drop
    context.bin_style = args.bin.lower()
    context.output_path = args.output
    context.class_file_path = sys.argv[1]
    context.nonclass_file_path = sys.argv[2]
    context.distinguishability_cutoff = float(sys.argv[3])
    return context

def main(context: CFDContext) -> None:
    class_file_path = context.class_file_path
    nonclass_file_path = context.nonclass_file_path
    distinguishability_cutoff = context.distinguishability_cutoff
    max_t_ways = context.max_t_ways
    gen_mvcs = context.gen_mvcs
    gen_graphs = context.gen_graphs

    class_file_name, _ = os.path.splitext(os.path.basename(class_file_path))
    nonclass_file_name, _ = os.path.splitext(os.path.basename(nonclass_file_path))
    context.class_file_name = class_file_name = sanitize_name(class_file_name, file='class')
    context.nonclass_file_name = nonclass_file_name = sanitize_name(nonclass_file_name, file='nonclass')
    max_t_ways = cast(int, max_t_ways)

    max_name_length = get_filename_limit()
    if len(class_file_name) + len(nonclass_file_name) + 20 > max_name_length:
        print_warning_message(context, "Your class and nonclass file names, when combined, will approach or exceed \
the limit of your system for file name/path lengths (typically 255). Please use shorter file names", True, True)

    if class_file_name == nonclass_file_name:
        nonclass_file_name += "_nc"
        context.nonclass_file_name = nonclass_file_name
        print_warning_message(context, "The class and nonclass file names are the same. \
Nonclass file name will be suffixed with '_nc'")

    if max_t_ways > 6 or max_t_ways < 1:
        print_warning_message(context, "Please choose an int value for max t-ways between 1-6 inclusive", True)

    if distinguishability_cutoff <= 1:
        print_warning_message(context, f"The distinguishability cutoff must be a real number greater than 1 \
(Currently {distinguishability_cutoff})", True)

    get_set_files(context)

    ncc = context.ncc
    if max_t_ways > ncc:
        print_warning_message(context,
        f"You are trying to get t={max_t_ways}-way data despite only having {ncc} variables", True)

    run_data(context)

    grid = cast(list[list[int]], context.data['grid'])
    missing_tway_combos = context.missing_tway_combos

    def assert_ge(a:float, b:float, description="", context="") -> None:

        """
        Asserts that a is greater than or equal to b, with a custom error message.
        """

        assert a >= b, f"Assertion failed: {a} >= {b} was False. {description} {context}".strip()

    for i in range(max_t_ways):
        grid_i0 = grid[i][0]
        grid_i1 = grid[i][1]
        grid_i2 = grid[i][2]
        grid_i3 = grid[i][3]
        grid_i4 = grid[i][4]
        grid_i5 = grid[i][5]
        grid_i6 = grid[i][6]

        assert_ge(grid_i0, grid_i1,
                "Max Possible VI >= Max Possible Class VI", f"(i={i})")
        assert_ge(grid_i0, grid_i2,
                "Max Possible VI >= Max Possible Nonclass VI", f"(i={i})")
        assert_ge(grid_i0, grid_i3,
                "Max Possible VI >= Present Class VI", f"(i={i})")
        assert_ge(grid_i0, grid_i4,
                "Max Possible VI >= Present Nonclass VI", f"(i={i})")
        assert_ge(grid_i0, grid_i5,
                "Max Possible VI >= Present Intersect VI", f"(i={i})")
        assert_ge(grid_i0, grid_i6,
                "Max Possible VI >= Distinguishing VI", f"(i={i})")
        assert_ge(grid_i1, grid_i3,
                "Max Possible Class VI >= Present Class VI", f"(i={i})")
        assert_ge(grid_i1, grid_i5,
                "Max Possible Class VI >= Present Intersect VI", f"(i={i})")
        assert_ge(grid_i2, grid_i4,
                "Max Possible Nonclass VI >= Present Nonclass VI", f"(i={i})")
        assert_ge(grid_i2, grid_i5,
                "Max Possible Nonclass VI >= Present Intersect VI", f"(i={i})")
        assert_ge(grid_i3, grid_i5,
                "Present Class VI >= Present Intersect VI", f"(i={i})")
        assert_ge(grid_i4, grid_i5,
                "Present Nonclass VI >= Present Intersect VI", f"(i={i})")

    for t in range(2, max_t_ways+1):
        assert_ge(grid[t-1][1], grid[t-1][3] + len(missing_tway_combos[f'{t}-way'][0]), 
            f"Max Possible {t}-way Class VI >= Present Class {t}-way VI({grid[t-1][3]}) + Missing Class {t}-way VI")
        assert_ge(grid[t-1][2], grid[t-1][4] + len(missing_tway_combos[f'{t}-way'][0]),
            f"Max Possible {t}-way Nonclass VI >= Present Nonclass {t}-way VI ({grid[t-1][4]}) + \
Missing Nonclass {t}-way VI")

    # Validation done, values obtained make mathematical sense (ie, max possible tways >= present tways, etc).
    # NOTE: This does not guarantee correctness of the data, however.

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

    now = datetime.now()
    formatted_time = now.strftime("%H:%M:%S")
    if not (context.silenced or context.silenced_ts):
        termcolor.cprint(f"TS: {message} - {formatted_time}", "green")

    sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    os.makedirs(sub_dir_name, exist_ok=True)
    new_file_name = f"Logs.txt"
    file_path = os.path.join(sub_dir_name, new_file_name)
    with open(file_path, "a") as file:
        file.write(f"TS: {message} - {formatted_time}\n")
        file.close()

def detect_header(df: pd.DataFrame) -> bool:

    """
    Detects if the first row is a header based on whether any of its values appear elsewhere in their columns.
    This is not perfect, but is typically good enough.
    Info / Warning statements may indicate when this has gone wrong
    """

    first_row = df.iloc[0]
    for column in df.columns:
        if first_row[column] in df[column].iloc[1:].values:
            return False
    return True

def remove_duplicate_rows(context: CFDContext, df: pd.DataFrame, is_class: bool) -> tuple[pd.DataFrame, list, bool]:

    """
    Checks for duplicate rows in the DataFrame.
    If duplicates are found, it prompts the user to either remove them, keep them, display
    them, or exit the program.
    If the user chooses to remove them, it returns a deduplicated DataFrame.
    If the user chooses to keep them, it returns the original DataFrame.
    If the user chooses to display them, it prints the duplicate rows.
    If the user chooses to exit, it terminates the program.
    """

    remove_dups = context.remove_dups
    logs = context.logs

    total_rows = len(df)
    name = context.class_file_name if is_class else context.nonclass_file_name

    duplicate_mask = df.duplicated(keep='first')
    duplicate_rows = df[duplicate_mask].copy()
    duplicate_rows_list = duplicate_rows.to_dict(orient='records')

    df_deduped = df.drop_duplicates(keep='first', ignore_index=True)
    deduped_rows = len(df_deduped)
    duplicates_found = total_rows - deduped_rows
    
    if duplicates_found > 0:
        response = ""
        if remove_dups:
            response = "R"
        plural = "rows" if duplicates_found > 1 else "row"
        print_info_message(context, f"Detected {duplicates_found} duplicate {plural} in {name}", not remove_dups)

        while response.upper() not in {"R", "K", "X", "D"}:
            response = input("Would you like to (R)emove them, (K)eep them, (D)isplay them, or e(X)it the program?\n> ")
            if response.upper() == 'D':
                print(f"Info: List of duplicate entries in {name}:\n")
                for row in duplicate_rows_list:
                    print("\t".join(str(value) for value in row.values()))
                response = input("Would you like to (R)emove them, (K)eep them, or e(X)it the program?\n> ")
        if response.upper() == 'R':
            print_info_message(context, f"Removing {duplicates_found} duplicate rows from {name}")
            return df_deduped, duplicate_rows_list, False
        elif response.upper() == 'K':
            return df, duplicate_rows_list, False
        elif response.upper() == 'X':
            # Returning this so that explicit type casting accepts the return elsewhere
            # True will always result in a system exit upon return
            return df, [], True
    else:
        if logs:
            print_info_message(context, f"No duplicate rows detected in {name}")
        return df, [], False
    return df, [], True # Unreachable, but added for type consistency

def remove_incomplete_rows(context: CFDContext, df: pd.DataFrame, is_class: bool) -> pd.DataFrame:

    """
    Removes rows with any missing values from the DataFrame.
    If no incomplete rows are found, it returns the original DataFrame.
    If incomplete rows are found, it prompts the user to either remove, keep, or display them.
    If the user chooses to remove them, it returns a cleaned DataFrame without those rows.
    If the user chooses to keep them, it returns the original DataFrame.
    If the user chooses to display them, all rows with missing data will be displayed and the user will be re-prompted.
    If the user chooses to exit, it terminates the program.
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

    plural = "rows" if num_incomplete > 1 else "row"
    print_info_message(context, f"Detected {num_incomplete} {plural} with missing values in {name}", not auto_remove)

    response = ""
    if auto_remove:
        response = "R"
    while response.upper() not in {"R", "K", "X", "D"}:
        response = input("Would you like to (R)emove them, (K)eep them, (D)isplay them, or e(X)it the program?\n> ")
        if response.upper() == 'D':
            print(f"Info: List of incomplete entries in {name}:\n")
            for row in incomplete_rows_list:
                print("\t".join(str(value) for value in row.values()))
            response = input("Would you like to (R)emove them, (K)eep them, or e(X)it the program?\n> ")

    if response.upper() == "R":
        df_cleaned = df.dropna()
        print_info_message(context, f"Removed {num_incomplete} incomplete {plural} from {name}")
        return df_cleaned
    elif response.upper() == "K":
        print_info_message(context, f"Keeping {num_incomplete} incomplete {plural} in {name} as-is")
        return df
    else:
        sys.exit(0)

def detect_possible_unintentionally_unique_variable_names(context: CFDContext):

    '''
    Detects the presence of values within a column differentiated solely by whitespace.
    Ex, " Yes " and "Yes". These will be treated as unique, however that may be unintentional due to a mistake in the 
    CSV. Warn the user for each column which contains values which meet this critera in the class or nonclass file.
    Apply the same process for values differentiated solely by the presence of quotes (\' or \").
    '''

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
            print_warning_message(context, f"Within the {variable_names[i]} column of the class file, one or more \
values are distinguished solely by whitespace: {class_diff_ws}. These will be treated as unique values")
        if len(nonclass_diff_ws) != 0:
            print_warning_message(context, f"Within the {variable_names[i]} column of the nonclass file, one or more \
values are distinguished solely by whitespace: {nonclass_diff_ws}. These will be treated as unique values")

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
            print_warning_message(context, f"Within the {variable_names[i]} column of the class file, one or more \
values are distinguished solely by the presence of quotes: {class_diff_qu}. These will be treated as unique values \
in an occasionally unpredictable manner")
        if len(nonclass_diff_qu) != 0:
            print_warning_message(context, f"Within the {variable_names[i]} column of the nonclass file, one or more \
values are distinguished solely by the presence of quotes: {nonclass_diff_qu}. These will be treated as unique values \
in an occasionally unpredictable manner")

def detect_possible_continuous(context: CFDContext, cont_threshold=0.5) -> None:

    """
    Detects columns in the DataFrame that may be continuous based on the number of unique values
    relative to the total number of rows.
    If the number of unique values is less than the threshold, it is likely categorical.
    If the number of unique values is greater than or equal to the threshold, it is likely continuous.
    If it is detected as continuous and binning is enabled, the user is given the option to bin the column.
    """

    variable_names = context.variable_names
    class_data = context.class_file_data
    nonclass_data = context.nonclass_file_data
    ncc = context.ncc
    nrc = context.nrc
    nrn = context.nrn
    manual_bin = True if context.bin_style == 'manual' else False

    num_rows = nrc if nrc >= 15 else 0
    num_rows += nrn if nrn >= 15 else 0
    # num_rows = 1

    if num_rows == 0: # Small data sets can be easily misinterpreted as continuous
        return

    for col in range(ncc):
        class_vals = [class_data[row][col] for row in range(len(class_data))]
        nonclass_vals = [nonclass_data[row][col] for row in range(len(nonclass_data))]
        all_vals = class_vals + nonclass_vals
        cl_unique = set(class_vals)
        nc_unique = set(nonclass_vals)
        union_unique = cl_unique.union(nc_unique)
        var_name = variable_names[col]
        num_unique = len(union_unique)

        if num_unique / (num_rows) >= cont_threshold:
            if not manual_bin:
                print_warning_message(context, f"Column '{var_name}' is likely continuous with {num_unique} \
unique values among {num_rows} considered instances.\nThe CFD tool does not effectively handle high cardinality \
variables.\n Consider binning (--bin) or otherwise transforming this column to reduce its cardinality")
            if manual_bin:
                num_all_vals = []
                try:
                    num_all_vals = [float(el) for el in all_vals]
                except:
                    try:
                        num_all_vals = [float(el.strip('\'"')) for el in all_vals]
                    except Exception as ex:
                        print_warning_message(context, f"The '{var_name}' column is likely continuous with {num_unique} \
unique values among {num_rows} considered instances. However, it does not contain strictly numerical data, making binning it \
automatically impossible. Consider binning or otherwise reducing this column's cardinality manually.\nException: {ex}")
                        continue
                print_info_message(context, f"The {var_name} column is a good candidate for binning with {num_unique} \
unique numerical values among {num_rows} considered instances", True)

                num_bins = -1
                print_info_message(context, f"To avoid binning this column, input a number of bins equal to its cardinality \
    ({num_unique}), or 0", True)
                while True:
                    num_bins = input(f"How many bins should the '{var_name}' column be divided into? > ")
                    try:
                        num_bins = int(num_bins)
                        if num_bins > num_unique or num_bins < 0:
                            print_info_message(context, f"You must chose a number of bins between 0 and the number \
of unique values it contains ({num_unique}). It is highly recommended to choose a number which reduces \
the feature's cardinality to a reasonable degree given the number values it holds and the number of instances between \
your files", True)
                            continue
                    except:
                        print_info_message(context, f"Please choose an integer between 1 and {num_unique} as the \
number of bins, or 0 to avoid binning", True)
                        continue
                    break
                if num_bins == num_unique or num_bins == 0:
                    print_info_message(context, f"Not performing binning on '{var_name}'")
                    continue

                clusters, centroids = kmeans1d.cluster(num_all_vals, num_bins)
                clusters = cast(list[int], clusters)
                final_groupings: dict[int, list[float]] = {}
                ranges: list[tuple[float, float]] = []
                for i in range(max(clusters)+1):
                    final_groupings[i] = []
                for elem, pos in zip(num_all_vals, clusters):
                    final_groupings[pos].append(elem)
                for i in range(max(clusters)+1):
                    ranges.append((min(final_groupings[i]), max(final_groupings[i])))

                context.feature_bin_ranges.append((var_name, num_unique, ranges))

                for idx, group in zip([i for i in range(nrc)], clusters[:nrc], strict=True):
                    context.class_file_data[idx][col] = str(ranges[group])
                for idx, group in zip([i for i in range(nrn)], clusters[nrc:], strict=True):
                    context.nonclass_file_data[idx][col] = str(ranges[group])

                print_info_message(context, f"The {var_name} column has been successfully divided into {num_bins} bins. \
To see the detailed breakdown of ranges, please see Info.txt")

def detect_possible_accidental_differentiation_column(context: CFDContext) -> None:

    '''
    Detect for the presence of a column meant to separate the data into class and nonclass files
    It would have all of one value in class and all of a different value in nonclass
    This can still be a valid column though, so warn only.
    '''

    class_file_data = context.class_file_data
    nonclass_file_data = context.nonclass_file_data
    ncc = context.ncc
    variable_names = context.variable_names
    auto_drop = context.auto_drop

    columns_to_drop: list[int] = []

    for i in range(ncc):
        unique_class = set()
        unique_nonclass = set()
        for row in class_file_data:
            unique_class.add(row[i])
        for row in nonclass_file_data:
            unique_nonclass.add(row[i])

        if len(unique_class) == 1 and len(unique_nonclass) == 1 and unique_class != unique_nonclass:
            columns_to_drop.append(i)
            if not auto_drop:
                print_warning_message(context, f"The {variable_names[i]} column contains only \"{unique_class.pop()}\" in \
the class file, and only \"{unique_nonclass.pop()}\" in the nonclass file. This may have been the column used to split \
the class and nonclass files.\nIf so, it should be removed as its values will not assist with calculations")
        elif len(unique_class) == 1 and unique_class == unique_nonclass:
            columns_to_drop.append(i)
            if not auto_drop:
                print_warning_message(context, f"The {variable_names[i]} column contains only one value for both the \
class and nonclass files: \"{unique_class.pop()}\". It should be removed as it will not assist with calculations")

    context.column_names_dropped = [variable_names[j] for j in columns_to_drop]

    if auto_drop:
        for idx in sorted(columns_to_drop, reverse=True):
            for row in context.class_file_data:
                del row[idx]
            for row in context.nonclass_file_data:
                del row[idx]
            del context.variable_names[idx]
        context.ncc = len(context.variable_names)
        if len(columns_to_drop) > 0:
            plural = ("columns were", "They are") if len(columns_to_drop) > 1 else ("column was", "It is")
            print_info_message(context, f"{len(columns_to_drop)} {plural[0]} dropped from the data. \
{plural[1]} logged in Info.txt")
        else:
            print_info_message(context, "No columns were dropped")

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

    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff

    sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
    variable_names = []

    if os.path.exists(sub_dir_name):
        if not overwrite:
            print_warning_message(context, f"The output folder {sub_dir_name} already exists. \
If you want to always overwrite it, please use the -o/--overwrite flag")
            response = input("Do you want to remove the old folder and continue? (Y/N): ")
            if response.upper() != "Y" and response.upper() != "YES":
                sys.exit(0)
        shutil.rmtree(sub_dir_name, ignore_errors=True) # sub_dir_name sanitized by this step, should be safe

    print_timestamp_message(context, "Begin class file loading")

    #
    # Class File
    #

    eng = 'c'
    sample = ''
    if len(delimiter) > 1:
        eng = 'python'
    try:
        with open(class_file_path, 'r') as f:
            sample = f.read(2048)
            f.close()
    except Exception as ex:
        print_warning_message(context, f"The expected class file was not found at '{class_file_path}'.\n\
Error Message: \"{str(ex).strip()}\"", True)

    sniffer = csv.Sniffer()
    try:
        dialect = sniffer.sniff(sample, delimiters=",;| \t")
    except Exception as ex:
        print_warning_message(context, f"Something went wrong when trying to determine the \
delimiter for '{class_file_name}'.\nPlease ensure that it is properly formatted and not empty.\n\
Error Message: \"{str(ex).strip()}\"", True)
        sys.exit(1) # Unreachable, necessary for knowing that dialect is not undefined

    if delimiter is not dialect.delimiter:
        print_warning_message(context, f"The expected delimiter '{delimiter}' was not found in '{class_file_name}'.\n\
Instead, the '{dialect.delimiter}' character was deduced to be the delimiting character.\n\
Please ensure that your CSVs either use a comma as their delimiter, or that you specify one using the delimiter flag.\n\
For tabs or spaces, use \"-d '\\s+'\"", True)

    try:
        class_df = pd.read_csv(class_file_path, sep=delimiter, header=None, dtype=str, engine=eng)
    except Exception as ex:
        print_warning_message(context, f"Something went wrong when trying to read '{class_file_name}' as a CSV.\n\
Please ensure that it is properly formatted and not empty.\nError message: \"{str(ex).strip()}\"", True)
        sys.exit(0) # Unreachable but added so that the compiler knows that class_df will always be defined

    class_df = remove_incomplete_rows(context, class_df, True)

    class_df, class_file_duplicates, exit = remove_duplicate_rows(context, class_df, True)
    if exit:
        sys.exit(0)

    if class_df.empty:
        print_warning_message(context, f"The class file '{class_file_name}' is empty after \
removing incomplete rows and duplicates", True)

    context.class_file_duplicates = class_file_duplicates

    if detect_header(class_df):
        context.has_header = True
        context.variable_names = variable_names = class_df.iloc[0].tolist()
        lengths = [len(str(name)) for name in variable_names]
        context.max_name_length = max(lengths)
        context.class_file_data = class_df.iloc[1:].values.tolist()
    else:
        context.class_file_data = class_df.values.tolist()

    class_file_data = context.class_file_data

    if len(class_file_data) == 0:
        print_warning_message(context, f"The class file, '{class_file_name}', is empty after header detection.\n\
Please ensure that the file contains data beyond a header", True)

    context.nrc = len(class_file_data)
    context.ncc = ncc = len(class_file_data[0])

    #
    # Nonclass File
    #

    print_timestamp_message(context, "Begin nonclass file loading")
    eng = 'c'
    if len(delimiter) > 1:
        eng = 'python'

    try:
        with open(nonclass_file_path, 'r') as f:
            sample = f.read(2048)
            f.close()
    except Exception as ex:
        print_warning_message(context, f"The expected nonclass file was not found at '{nonclass_file_path}'.\n\
Error Message: \"{str(ex).strip()}\"", True)

    sniffer = csv.Sniffer()
    try:
        dialect = sniffer.sniff(sample, delimiters=",;| \t")
    except Exception as ex:
        print_warning_message(context, f"Something went wrong when trying to determine the \
delimiter for '{nonclass_file_name}'.\nPlease ensure that it is properly formatted and not empty.\n\
Error Message: \"{str(ex).strip()}\"", True)
        sys.exit(1) # Unreachable, necessary for knowing that dialect is not undefined

    if delimiter is not dialect.delimiter:
        print_warning_message(context, f"The expected delimiter '{delimiter}' was not found in '{nonclass_file_name}'.\n\
Instead, the '{dialect.delimiter}' character was deduced to be the delimiting character.\n\
Please ensure that your CSVs either use a comma as their delimiter, or that you specify one using the delimiter flag.\n\
For tabs or spaces, use \"-d '\\s+'\"", True)

    try:
        nonclass_df = pd.read_csv(nonclass_file_path, sep=delimiter, header=None, dtype=str, engine=eng)
    except Exception as ex:
        print_warning_message(context, f"Something went wrong when trying to read '{nonclass_file_name}' as a CSV.\n\
Please ensure that it is properly formatted and not empty.\nError message: \"{str(ex).strip()}\"", True)
        sys.exit(0) # Unreachable but added so that the compiler knows that nonclass_df will always be defined

    nonclass_df = remove_incomplete_rows(context, nonclass_df, False)

    nonclass_df, nonclass_file_duplicates, exit = remove_duplicate_rows(context, nonclass_df, False)
    if exit:
        sys.exit(0)

    if nonclass_df.empty:
        print_warning_message(context, f"The nonclass file '{nonclass_file_name}' is \
empty after removing incomplete rows and duplicates", True)

    context.nonclass_file_duplicates = nonclass_file_duplicates

    if detect_header(nonclass_df):

        variable_names_nonclass = nonclass_df.iloc[0].tolist()

        if context.has_header and (len(context.variable_names) != len(variable_names_nonclass)):
            print_warning_message(context, f"Both files must refer to the same number of variables.\n\
'{context.class_file_name}' refers to {len(context.variable_names)} variables while \
'{context.nonclass_file_name}' refers to {len(variable_names_nonclass)} variables", True)
        elif context.has_header and (context.variable_names != variable_names_nonclass):
            print_warning_message(context, f"Both files must refer to the same variables:\n\
'{context.class_file_name}' refers to: {variable_names}\n\
'{context.nonclass_file_name}' refers to: {variable_names_nonclass}", True)

        context.has_header = True
        context.nonclass_file_data = nonclass_df.iloc[1:].values.tolist()
    else:
        context.nonclass_file_data = nonclass_df.values.tolist()

    nonclass_file_data = context.nonclass_file_data

    if len(nonclass_file_data) == 0:
        print_warning_message(context, f"The nonclass file, '{nonclass_file_name}', is empty after header detection.\n\
Please ensure that the file contains data beyond a header", True)
    
    context.nrn = len(nonclass_file_data)
    ncn = len(nonclass_file_data[0])

    #
    # Misc Error Check
    #

    if ncn != ncc:
        print_warning_message(context, f"Both files must refer to the same variables.\n\
'{context.class_file_name}' contains {ncc} columns while '{context.nonclass_file_name}' contains {ncn}", True)

    if variable_names != [] and not verbose:
        print_warning_message(context, "A header was detected AND REMOVED FROM DATA in one or both files, \
but verbose (-v) mode was not enabled")

    if variable_names == [] or not verbose:
        context.variable_names = []
        if verbose:
            print_warning_message(context, "Verbose mode was enabled but NO VARIABLE NAMES were detected. \
Using default variable names")
        for i in range(ncc):
            context.variable_names.append(f"Var {i}")

    # Check for multiple variables with the same name
    seen = set()
    duplicates = []
    for name in context.variable_names:
        if name in seen:
            duplicates.append(name)
        else:
            seen.add(name)
    if len(duplicates) > 0:
        plural = "variables have" if len(duplicates) > 1 else "variable has"
        print_warning_message(context, f"The following {plural} multiple instances with the same name:\n\
{[f'{name}' for name in duplicates]}\nPlease ensure all variables have unique names", True)

    class_set = {str([val for val in inner_list]) for inner_list in class_file_data}
    nonclass_set = {str([val for val in inner_list]) for inner_list in nonclass_file_data}

    if class_set == nonclass_set:
        print_warning_message(context, "Class and nonclass files are identical. Please provide different files", True)
    elif class_set.issubset(nonclass_set):
        print_warning_message(context, f"'{context.class_file_name}' is a subset of '{context.nonclass_file_name}'.\n\
Please ensure that the class file contains unique data that is not present in the nonclass file", True)
    elif nonclass_set.issubset(class_set):
        print_warning_message(context, f"'{context.nonclass_file_name}' is a subset of '{context.class_file_name}'.\n\
Please ensure that the nonclass file contains unique data that is not present in the class file", True)

    detect_possible_continuous(context)
    detect_possible_accidental_differentiation_column(context)
    detect_possible_unintentionally_unique_variable_names(context)

    # Sanitize Variable Names
    san_names = \
        [sanitize_name(var_name) if isinstance(var_name, str) else var_name for var_name in context.variable_names]
    old_names = [item for item in context.variable_names if item not in san_names]

    size_diff = len(context.variable_names) - len(set(san_names))
    if size_diff != 0:
        print_warning_message(context, f"Sanitizing variable names resulted in {size_diff} variables \
with the same name.\nPlease ensure that your variable names are not differentiated by characters \
which must be escaped (ex, quotes, slashes, semicolons, etc.)", True)

    if len(old_names) != 0:
        new_names = [item for item in san_names if item not in context.variable_names]
        plural = "names have" if len(old_names) > 1 else "name has"
        print_info_message(context, f"{len(old_names)} variable {plural} been santized to prevent \
unpredictable parsing")
        for i in range(len(old_names)):
            print_info_message(context, f"{old_names[i]} ==> {new_names[i]}")

    context.variable_names = san_names
    print_timestamp_message(context, "Files loaded")

class CombinationCounter:
    def __init__(self, file_data: list[list[str]]):
        self.data: list[list[str]] = file_data
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

            for row in tq(self.data, disable=hide_bar):
                if timeout and time.time() - start_time > 3:
                    return False
                indexed_values: list[ValueCombo_Tuple_index_str] = \
                    [(index, value) for index, value in enumerate(row) if pd.notnull(value)]
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

    for t in range(1, max_ways+1):
        frozen_combos[f'{t}-way'] = [frozenset(combo) for combo, _, _, _, _ in distin_tway_combos[f'{t}-way'][is_nonclass]]

    def do_calculation(hide_bar: bool, start: float) -> tuple[bool, list[int]]:
        
        cl = "Nonclass" if is_nonclass else "Class"
        t_counts: dict[str, int] = {f'{t}-way': 0 for t in range(1, 7)}

        for row in tq(data, desc=f"{cl} Counting Distinguishing", disable=hide_bar):
            if start != 0 and time.time() - start > 3:
                return False, []
            for t in range(1, 7):
                if t > max_ways:
                    break
                row_set = frozenset((index, row[index]) for index in range(len(row)))
                found = any(combo.issubset(row_set) for combo in frozen_combos[f'{t}-way'])
                if found:
                    t_counts[f'{t}-way'] += 1
        return True, [t_counts[f'{t}-way'] for t in range(1, 7)]

    if logs and not silent:
        res = do_calculation(True, time.time())
        if res[0]:
            return res[1]
        return do_calculation(False, 0)[1]
    else:
        return do_calculation(True, 0)[1]

def generate_output_statements(context: CFDContext, 
        class_distinguishing_combos: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]],
        nonclass_distinguishing_combos: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, int, int]], 
        way=0) -> None:

    """
    Generates output statements for unique and distinguishing combinations
    based on the provided class and nonclass distinguishing combinations.
    The output is formatted as CSV strings and added to the appropriate file in the context.
    """

    verbose = context.verbose
    variable_names = context.variable_names
    logs = context.logs
    silent = context.silenced or context.silenced_ts

    unique_combos: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, str]] = []
    distinguishing_combos_list: list[tuple[tuple[ValueCombo_Tuple_index_str, ...], float, float, float]] = []
    total_iter = len(class_distinguishing_combos) + len(nonclass_distinguishing_combos)

    def do_calculation(hide_bar: bool, timeout: bool) -> bool:
        start_time = time.time()

        with tq(total=total_iter, desc=f"{way}-way Calculation Progress", disable=hide_bar) as pbar:
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

    # Sort unique DVCs by frequency in the respective file
    unique_combos.sort(key=lambda x: x[1], reverse=True)

    # NOTE: Sort distinguishing combos by frequency difference in decreasing order
    # distinguishing_combos_list.sort(key=lambda x: x[3], reverse=True) # (uncomment this to use this ordering instead)

    # Sort distinguishing combos by frequency in the respective file 
    # NOTE: (comment this out when using the other ordering )
    distinguishing_combos_list.sort(key=lambda x: max(x[1], x[2]), reverse=True) 

    total_iter = len(unique_combos) + len(distinguishing_combos_list)

    def do_appending(hide_bar: bool, timeout: bool) -> bool:
        start_time = time.time()

        with tq(total=total_iter, desc=f"{way}-way DVC Progress", disable=hide_bar) as pbar:
            for combo, freq, class_type in unique_combos:
                i = 1 if class_type == "Class" else 0
                if not verbose:
                    csv_str = ";".join(f"({index}, {value})" for index, value in combo)
                    get_the_right_file(context, way)[0].append(f"U;{i};{csv_str};{freq:.4f};;")
                else:
                    csv_str = ";".join(f"({variable_names[cast(int, index)]}, {value})" for index, value in combo)
                    get_the_right_file(context, way)[0].append(f"U;{i};{csv_str};{freq:.4f};;")
                pbar.update(1)
                if timeout and time.time() - start_time > 3:
                    return False

            for combo, freq_a, freq_b, diff in distinguishing_combos_list:
                h_freq = freq_a if freq_a > freq_b else freq_b
                i = 1 if freq_a > freq_b else 0

                if not verbose:
                    csv_str = ";".join(f"({index}, {value})" for index, value in combo)
                    get_the_right_file(context, way)[0].append(f"D;{i};{csv_str};{h_freq:.4f};{diff:.4f};")
                else:
                    csv_str = ";".join(f"({variable_names[index]}, {value})" for index, value in combo)
                    get_the_right_file(context, way)[0].append(f"D;{i};{csv_str};{h_freq:.4f};{diff:.4f};")
                pbar.update(1)
                if timeout and time.time() - start_time > 3:
                    return False
            return True

    print_timestamp_message(context, f"Generating {way}-way DVC statements")
    if logs and not silent:
        if not do_appending(True, True):
            get_the_right_file(context, way)[0].clear()
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
        values_product = []

        for i in range(2, 7):
            if t == i:
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
        all_possible_tway_class: dict[tuple[ValueIndex, ...], list[tuple[ValueString, ...]]], 
        all_possible_tway_nonclass: dict[tuple[ValueIndex, ...], list[tuple[ValueString, ...]]],
        t: int) -> tuple[list[tuple[tuple[str, ...], list[int]]], list[tuple[tuple[str, ...], list[int]]]]:

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

    if not context.gen_mvcs or t > context.max_t_ways:
        return [], []

    missing_tway_class: list[tuple[tuple[ValueString, ...], list[ValueIndex]]] = []
    missing_tway_nonclass: list[tuple[tuple[ValueString, ...], list[ValueIndex]]] = []

    def is_valid_combo(values: tuple[str, ...]) -> bool:

        """
        Checks if all values in the combination are not null.
        Returns True if all values are not null, otherwise False.
        """
        return all(pd.notnull(v) for v in values)

    def normalized(combo: tuple[ValueCombo_Tuple_index_str, ...]) -> tuple[ValueCombo_Tuple_index_str, ...]:

        """
        Normalizes the combination by sorting it based on the first element of each tuple.
        """

        ret = tuple(sorted(combo, key=lambda x: x[0]))
        return ret

    norm_class_t = {normalized(c) for c in combination_counts_class[f'{t}-way']}
    norm_nonclass_t = {normalized(c) for c in combination_counts_nonclass[f'{t}-way']}

    total_iters = 0
    for _, values_list in all_possible_tway_class.items():
        total_iters += len(values_list)
    for _, values_list in all_possible_tway_nonclass.items():
        total_iters += len(values_list)

    print_timestamp_message(context, f"Beginning {t}-way missing value combinations")
    def do_calculation(hide_bar: bool, timeout: bool) -> tuple[bool, 
            list[tuple[tuple[ValueString, ...], list[ValueIndex]]], 
            list[tuple[tuple[ValueString, ...], list[ValueIndex]]]]:

        pbar = tq(total=total_iters, desc=f"{t}-way MVCs", disable=hide_bar)
        missing_tway_class.clear()
        missing_tway_nonclass.clear()
        start_time = time.time()

        for indices, values_list in all_possible_tway_class.items():
            for values in values_list:
                if timeout and time.time() - start_time > 3:
                    return False, [], []
                pbar.update(1)
                if not is_valid_combo(values):
                    continue
                combo = tuple(zip(indices, values))
                if normalized(combo) not in norm_class_t:
                    missing_tway_class.append((values, list(indices)))

        for indices, values_list in all_possible_tway_nonclass.items():
            for values in values_list:
                if timeout and time.time() - start_time > 3:
                    return False, [], []
                pbar.update(1)

                if not is_valid_combo(values):
                    continue

                combo = tuple(zip(indices, values))
                if normalized(combo) not in norm_nonclass_t:
                    missing_tway_nonclass.append((values, list(indices)))
        return True, missing_tway_class, missing_tway_nonclass

    res: tuple[bool, list[tuple[tuple[ValueString, ...], list[ValueIndex]]], 
                     list[tuple[tuple[ValueString, ...], list[ValueIndex]]]] = (True, [], [])
    if logs and not silent:
        res = do_calculation(True, True)
        if not res[0]:
            res = do_calculation(False, False)
    else:
        res = do_calculation(True, False)
    return res[1], res[2]

def get_the_right_file(context: CFDContext, t: int) -> tuple[list[str], str]:

    """
    Returns the appropriate CSV file and header string based on the value of t.
    """

    var_lst = [f"Variable{i}" for i in range(1,t+1)]
    var_str = ";".join(var_lst)
    final_str = f"Type;Class;{var_str};Frequency;Frequency_Difference;\n"
    csv_ret = f"csv_print_{t}way"
    return getattr(context, csv_ret), final_str

def find_common_entries(context: CFDContext) -> list[tuple[tuple[str, ...], dict[str, int]]]:

    """
    Find entries that appear in both class and nonclass files, and record their counts.
    """

    class_file_data = context.class_file_data
    nonclass_file_data = context.nonclass_file_data
    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff

    class_data_tuples = [tuple(entry) for entry in class_file_data]
    nonclass_data_tuples = [tuple(entry) for entry in nonclass_file_data]

    # Count entries in class data
    class_counts: dict[tuple[str, ...], int] = defaultdict(int)
    for entry in class_data_tuples:
        class_counts[entry] += 1

    # Count entries in nonclass data
    nonclass_counts: dict[tuple[str, ...], int] = defaultdict(int)
    for entry in nonclass_data_tuples:
        nonclass_counts[entry] += 1

    # Find common entries and their counts
    common_entries: list[tuple[tuple[str, ...], dict[str, int]]] = []
    for entry in class_counts:
        if entry in nonclass_counts:
            common_entries.append(
                (entry,
                {'class_count': class_counts[entry],
                 'nonclass_count': nonclass_counts[entry]}
            ))

    if common_entries != []:
        plural = ("entry", "it") if len(common_entries) == 1 else ("entries", "them")
        print_warning_message(context, f"Found {len(common_entries)} common {plural[0]} between class and nonclass \
files. To view {plural[1]}, check the Info.txt output file")
        
        sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
        os.makedirs(sub_dir_name, exist_ok=True)
        new_file_name = f"Common_Entries.csv"
        file_path = os.path.join(sub_dir_name, new_file_name)
        with open(file_path, 'w',) as file:
            file.write("Entry;Class_Count;Nonclass_Count\n")
            for entry, counts in common_entries:
                entry_str = "(" + ",".join(str(value) for value in entry) + ")"
                file.write(f"{entry_str};{counts['class_count']};{counts['nonclass_count']}\n")
            file.close()

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

    # Adjust the tick interval to be "nicer" (ex, 0.1, 0.2, 0.25, 0.5, 1, 2, 5, 10)
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

            if cl != []:
                cl = [cl[0]] + cl + [cl[-1]] # These are done so that the steps extend to the graph edges
            if nc != []:
                nc = [nc[0]] + nc + [nc[-1]] # Only really noticible for very small datasets
            if un != []:
                un = [un[0]] + un + [un[-1]]

            def set_the_x_axis(ax: mpl_axes.Axes, lst: list[float]):
                current_xticks: list[int] = []
                tick_labels: list[str] = []
                max_num = max(num_each_t_way)
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
            ax1.step(range(len(cl)), cl, color='blue', label=f'Class {name}', alpha=0.7, where='mid')
            ax1.set_title(f'Class {name} for All T-Way Combos')
            set_the_x_axis(ax1, cl)
            ax1.set_ylabel(f'{name}')
            ax1.legend(loc='best')
            ax1.grid(axis='y')
            if cl != []:
                safe_set_ylim(ax1, cl, False)

            print_timestamp_message(context, f"Generating Nonclass Value Combo {name} Graph")
            ax2.step(range(len(nc)), nc, color='red', label=f'Nonclass {name}', alpha=0.7, where='mid')
            ax2.set_title(f'Nonclass {name} for All T-Way Combos')
            set_the_x_axis(ax2, nc)
            ax2.set_ylabel(f'{name}')
            ax2.legend(loc='best')
            ax2.grid(axis='y')
            if nc != []:
                safe_set_ylim(ax2, nc, False)

            print_timestamp_message(context, f"Generating Difference Value Combo {name} Graph")
            ax3.step(range(len(un)), un, color='purple', label=f'Difference of Class and Nonclass {name}', alpha=0.7, where='mid') 
            ax3.set_title(f'Difference of {name} (Class - Nonclass) for All T-way Combos')
            set_the_x_axis(ax3, un)
            ax3.set_ylabel(f'Diff of {name}')
            ax3.legend(loc='best')
            ax3.grid(axis='y')
            if freq_u != []:
                safe_set_ylim(ax3, un, False)
            ax3.axhline(0, color='black', linestyle='-', linewidth=2.5)

            sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
            graphs_dir = os.path.join(sub_dir_name, "Graphs")
            os.makedirs(graphs_dir, exist_ok = True)
            file_name = os.path.join(graphs_dir, f"Value_Combo_{name}.png")
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
    Returns the frequencies for class, nonclass, and their difference.
    """

    gen_graphs = context.gen_graphs
    class_file_name = context.class_file_name
    nonclass_file_name = context.nonclass_file_name
    distinguishability_cutoff = context.distinguishability_cutoff
    max_ways = context.max_t_ways

    if t > max_ways or not gen_graphs:
        return

    distinguishing_class_combos = context.distin_tway_combos[f"{t}-way"][0]
    distinguishing_nonclass_combos = context.distin_tway_combos[f"{t}-way"][1]

    # Extract the combos and their frequencies
    class_combos = {combo: (freq_a, freq_b, count_a, count_b)
        for combo, freq_a, freq_b, count_a, count_b in distinguishing_class_combos}
    nonclass_combos = {combo: (freq_a, freq_b, count_a, count_b)
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

    if freq_cl != []:
        freq_cl = [freq_cl[0]] + freq_cl + [freq_cl[-1]]
        num_cl = [num_cl[0]] + num_cl + [num_cl[-1]]
    if freq_nc != []:
        freq_nc = [freq_nc[0]] + freq_nc + [freq_nc[-1]]
        num_nc = [num_nc[0]] + num_nc + [num_nc[-1]]
    if freq_u != []:
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

            ax1.step(range(len(cl)), cl, color='blue', label=f'Class {name}', where='mid')
            ax1.set_title(f'Class {name} for Distinguishing {t}-way Combos')
            set_the_x_axis(ax1, cl)
            ax1.set_ylabel(f'{name}')
            ax1.legend(loc='best')
            ax1.grid(True, which='major', linestyle='--', linewidth=0.5)
            if cl != []:
                safe_set_ylim(ax1, cl, True)

            ax2.step(range(len(nc)), nc, color='red', label=f'Nonclass {name}', where='mid')
            ax2.set_title(f'Nonclass {name} for Distinguishing {t}-way Combos')
            set_the_x_axis(ax2, nc)
            ax2.set_ylabel(f'{name}')
            ax2.legend(loc='best')
            ax2.grid(True, which='major', linestyle='--', linewidth=0.5)
            if nc != []:
                safe_set_ylim(ax2, nc, True)

            ax3.step(range(len(un)), un, color='purple', label=f'Difference of {name}', where='mid') 
            ax3.set_title(f'Difference in {name} (Class - Nonclass) for Distinguishing {t}-way Combos')
            set_the_x_axis(ax3, un)
            ax3.set_ylabel(f'Diff of {name}')
            ax3.legend(loc='best')
            ax3.grid(True, which='major', linestyle='--', linewidth=0.5)
            if un != []:
                safe_set_ylim(ax3, un, True)
            ax3.axhline(0, color='black', linestyle='-', linewidth=2.5)

            sub_dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
            graphs_dir = os.path.join(sub_dir_name, "Graphs")
            os.makedirs(graphs_dir, exist_ok=True)
            sub_dir_freq = os.path.join(graphs_dir, f"Distinguishing {name}")
            os.makedirs(sub_dir_freq, exist_ok=True)
            file_name = os.path.join(sub_dir_freq, f"Distinguishing_{name}_{t}_way.png")
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
                print_warning_message(context, f"Something went wrong when filtering distinguishing combinations. \
One of DVCs, {combo}, does not have any data associated with it.\nProgram will continue, but be warned that \
results are likely compromised\nException Caught: {ex}") # Has never happened in testing thankfully
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

    # Class coverage out of max all ways
    axs[0][0].step(t_levels_ext, percent_cl_of_all_ext, where='mid', label='Class Coverage', color='blue')
    axs[0][0].set_ylabel('Class Coverage (%)')
    axs[0][0].grid(True, which='both', linestyle='--', linewidth=0.5)
    axs[0][0].set_title('Present Class VCs Out Of Max Union VCs')
    for i in range(1, max_ways+1):
        if percent_cl_of_all_ext[i] == int(percent_cl_of_all_ext[i]):
            text = f"{int(percent_cl_of_all_ext[i])}"
        else:
            text = f"{round(percent_cl_of_all_ext[i], 2)}"
        axs[0][0].text(t_levels_ext[i], percent_cl_of_all_ext[i] + 3, text, ha='center', va='center')

    # Class coverage out of max class ways
    axs[0][1].step(t_levels_ext, percent_cl_of_max_cl_ext, where='mid', label='Class Coverage', color='blue')
    axs[0][1].set_ylabel('Class Coverage (%)')
    axs[0][1].grid(True, which='both', linestyle='--', linewidth=0.5)
    axs[0][1].set_title('Present Class VCs Out Of Max Class VCs')
    for i in range(1, max_ways+1):
        if percent_cl_of_max_cl_ext[i] == int(percent_cl_of_max_cl_ext[i]):
            text = f"{int(percent_cl_of_max_cl_ext[i])}"
        else:
            text = f"{round(percent_cl_of_max_cl_ext[i], 2)}"
        axs[0][1].text(t_levels_ext[i], percent_cl_of_max_cl_ext[i] + 3, text, ha='center', va='center')

    # Nonclass coverage out of max all ways
    axs[1][0].step(t_levels_ext, percent_nc_of_all_ext, where='mid', label='Nonclass Coverage', color='red')
    axs[1][0].set_ylabel('Nonclass Coverage (%)')
    axs[1][0].grid(True, which='both', linestyle='--', linewidth=0.5)
    axs[1][0].set_title('Present Nonclass VCs Out Of Max Union VCs')
    for i in range(1, max_ways+1):
        if percent_nc_of_all_ext[i] == int(percent_nc_of_all_ext[i]):
            text = f"{int(percent_nc_of_all_ext[i])}"
        else:
            text = f"{round(percent_nc_of_all_ext[i], 2)}"
        axs[1][0].text(t_levels_ext[i], percent_nc_of_all_ext[i] + 3, text, ha='center', va='center')

    # Nonclass coverage out of max nonclass ways
    axs[1][1].step(t_levels_ext, percent_nc_of_max_nc_ext, where='mid', label='Nonclass Coverage', color='red')
    axs[1][1].set_ylabel('Nonclass Coverage (%)')
    axs[1][1].grid(True, which='both', linestyle='--', linewidth=0.5)
    axs[1][1].set_title('Present Nonclass VCs Out Of Max Nonclass VCs')
    for i in range(1, max_ways+1):
        if percent_nc_of_max_nc_ext[i] == int(percent_nc_of_max_nc_ext[i]):
            text = f"{int(percent_nc_of_max_nc_ext[i])}"
        else:
            text = f"{round(percent_nc_of_max_nc_ext[i], 2)}"
        axs[1][1].text(t_levels_ext[i], percent_nc_of_max_nc_ext[i] + 3, text, ha='center', va='center')

    # Union coverage
    axs[2][0].step(t_levels_ext, percent_union_ext, where='mid', label='Union Coverage', color='purple')
    axs[2][0].set_ylabel('Union Coverage (%)')
    axs[2][0].grid(True, which='both', linestyle='--', linewidth=0.5)
    axs[2][0].set_title('Present Class + Nonclass VCs Out Of Max Union VCs')
    for i in range(1, max_ways+1):
        if percent_union_ext[i] == int(percent_union_ext[i]):
            text = f"{int(percent_union_ext[i])}"
        else:
            text = f"{round(percent_union_ext[i], 2)}"
        axs[2][0].text(t_levels_ext[i], percent_union_ext[i] + 3, text, ha='center', va='center')

    axs[2][1].axis('off')

    for i in range(3):
        for j in range(2):
            if i == 2 and j == 1:
                break
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
    dir_name = f"output\\{class_file_name}-{nonclass_file_name}-{distinguishability_cutoff}"
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
 
    print_timestamp_message(context, "Beginning class calculations")
    counter_class = CombinationCounter(class_file_data)
    counter_class.count_combinations(context)
    combination_counts_class = counter_class.get_combination_counts()
    context.combination_counts_class = combination_counts_class

    print_timestamp_message(context, "Beginning nonclass calculations")
    counter_nonclass = CombinationCounter(nonclass_file_data)
    counter_nonclass.count_combinations(context)
    combination_counts_nonclass = counter_nonclass.get_combination_counts()
    context.combination_counts_nonclass = combination_counts_nonclass

    print_timestamp_message(context, f"Discovering common entries")
    common_entries = find_common_entries(context)
    context.common_entries = common_entries

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

    for t in range(1, max_ways+1):
        generate_output_statements(
            context,
            distinguishing_tway_combos[f'{t}-way'][0],
            distinguishing_tway_combos[f'{t}-way'][1],
            t
        )

    missing_tway_combos: dict[str, tuple[list[tuple[tuple[str, ...], list[int]]],
                                         list[tuple[tuple[str, ...], list[int]]]]] = {}

    for t in range(2, 7):
        key = f"{t}-way"
        results = find_missing_combos(context, max_class_tway_combos[t-2], max_nonclass_tway_combos[t-2], t)
        missing_tway_combos[key] = (results[0], results[1])

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

    required_packages: list[str] = [
        'pandas', # Dataframes for reading CSV data
        'numpy', # Mathematical operations (mostly graph related)
        'matplotlib.pyplot', # Graph creation
        'matplotlib.axes', # Type enforcing the axes object
        'matplotlib_venn', # Venn diagram graphs specifically
        'termcolor', # Colored terminal output
        'tqdm', # Progress bars in terminal when logging output and operation takes > 3 seconds
        'kmeans1d' # For binning continuous numerical data
    ]
    for pkg in required_packages:
        install_and_import(context, pkg)

    main(context)
