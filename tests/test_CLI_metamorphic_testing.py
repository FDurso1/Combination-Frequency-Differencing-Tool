import os
import pytest
from setup.CLI_testing import gen_x_5_data, base_testing, random_testing, line_in_csv
import random
import shutil

@pytest.fixture(scope="module")
def setup_generated_folders():

    output_5 = gen_x_5_data()
    random.seed(404)
    random_float_1 = random.uniform(2, 10)
    r_cutoff_1 = f"{random_float_1:.1f}"
    random_float_2 = random.uniform(2, 10)
    r_cutoff_2 = f"{random_float_2:.1f}"
    higher = max(r_cutoff_1, r_cutoff_2)
    lower = min(r_cutoff_1, r_cutoff_2)
    higher_folder = random_testing(higher)
    lower_folder = random_testing(lower)
    yield output_5, higher_folder, lower_folder
    
    # Cleanup
    
    for folder in [output_5, higher_folder, lower_folder]:
        if os.path.exists(folder):
            shutil.rmtree(folder)
    if os.path.exists('tempCodeRunnerFile.py'):
        os.remove('tempCodeRunnerFile.py')
    

def get_dvc_file(folder, tway):
    return os.path.join(folder, "DVCs", f"{tway}-way_DVCs.csv")

def extract_dvc_lines(csv_file):
    with open(csv_file, encoding="utf-8") as f:
        return set(line.strip() for line in f if line.strip())

def test_basic_testing_runs(setup_generated_folders):
    output_5, higher_folder, lower_folder = setup_generated_folders
    
    # Should not raise exceptions
    base_testing(output_5)
    base_testing(higher_folder)
    base_testing(lower_folder)

def test_1way_dvcs_metamorphic(setup_generated_folders):
    _, higher_folder, lower_folder = setup_generated_folders
    higher_1way = extract_dvc_lines(get_dvc_file(higher_folder, 1))
    lower_1way = extract_dvc_lines(get_dvc_file(lower_folder, 1))
    # Increasing cutoff: 1-way DVCs should remain constant or decrease
    assert higher_1way <= lower_1way

def test_2way_dvcs_metamorphic(setup_generated_folders):
    _, higher_folder, lower_folder = setup_generated_folders
    higher_2way = extract_dvc_lines(get_dvc_file(higher_folder, 2))
    lower_2way = extract_dvc_lines(get_dvc_file(lower_folder, 2))
    higher_1way = extract_dvc_lines(get_dvc_file(higher_folder, 1))
    lower_1way = extract_dvc_lines(get_dvc_file(lower_folder, 1))
    # If 1-way DVCs remain constant, 2-way DVCs should also remain constant or decrease
    if higher_1way == lower_1way:
        assert higher_2way <= lower_2way
    # If 2-way DVCs increase, they must involve values that were previously 1-way DVCs but are no longer
    if len(higher_2way) > len(lower_2way):
        diff = higher_2way - lower_2way
        
        # Each new 2-way DVC must involve at least one variable/value that was a 1-way DVC in lower but not in higher
        def extract_var_val_pairs(dvc_line: str):
            # Extract (variable, value) pairs from a DVC line
            pairs = []
            for part in dvc_line.split(";"):
                if "(" in part and "," in part and ")" in part:
                    try:
                        var, val = part.strip("()").split(",", 1)
                        pairs.append((var.strip(), val.strip()))
                    except ValueError:
                        continue
            return pairs

        lower_1way_pairs = set()
        for line in (lower_1way - higher_1way):
            lower_1way_pairs.update(extract_var_val_pairs(line))

        for dvc in diff:
            dvc_pairs = extract_var_val_pairs(dvc)
            try:
                assert any(pair in lower_1way_pairs for pair in dvc_pairs)
            except:
                print(f"DEBUG: {dvc}")
                print(dvc_pairs)
                assert(False)
            
def test_dvc_file_exists_and_nonempty(setup_generated_folders):
    for folder in setup_generated_folders:
        for tway in [1, 2]:
            dvc_file = get_dvc_file(folder, tway)
            assert os.path.exists(dvc_file)
            lines = extract_dvc_lines(dvc_file)
            assert len(lines) > 0

def test_line_in_csv_function(tmp_path):
    # Create a dummy CSV
    csv_file = tmp_path / "test.csv"
    content = ["a,b,c", "d,e,f", "g,h,i"]
    csv_file.write_text("\n".join(content), encoding="utf-8")
    # Test line_in_csv
    assert line_in_csv(str(csv_file), line="d,e,f")
    assert not line_in_csv(str(csv_file), line="x,y,z")
    assert line_in_csv(str(csv_file), size=3)
    assert not line_in_csv(str(csv_file), size=2)