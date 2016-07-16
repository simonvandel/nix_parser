# Tested with Python 3.5
# This script checks all nix test cases against the reference nix parser to check for its validity

import glob
import subprocess
import sys

nix_files = glob.iglob("test_cases/**/*.nix", recursive=True)
for nix_file in nix_files:
    # we do not want to validate all files
    if not nix_file.endswith("_ignore_validate.nix"):
        completed_process = subprocess.run(["nix-instantiate", "--parse", nix_file])
        if completed_process.returncode != 0:
            sys.exit("ERROR: " + nix_file + " does not seem to be a valid Nix file!")
