# %%
import glob
import re
import os
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("logDir")
parser.add_argument("outputPath")
args = parser.parse_args()

#
# Example)
# python3 summary.py reducible/log reducible/summary.csv
# python3 summary.py reducible/contraction_log reducible/contraction_summary.csv
# python3 summary.py nconfs/log nconfs/summary.csv
# 

xPattern = re.compile(r"critical")
dPattern = re.compile(r"D\-reducible!")
cPattern = re.compile(r"Contracted:([0-9 ,]+)")
nPattern = re.compile(r"not C\-reducible.")
with open(args.outputPath, "w") as sum:
    for path in sorted(glob.glob(os.path.join(args.logDir, "*.log"))):
        name = os.path.splitext(os.path.basename(path))[0]
        with open(path, "r") as f:
            finished = False
            conts = None
            error = False
            for line in f:
                if xPattern.search(line):
                    error = True
                    break
                if dPattern.search(line):
                    conts = []
                    break
                m = cPattern.search(line)
                if m:
                    cont = list(map(lambda s: s.strip(), m.group(1).split(",")))
                    if conts is None:
                        conts = []
                        conts.append(cont)
                    elif len(cont) <= len(conts[0]) + 1:
                        conts.append(cont)
                    else:
                        break
                if nPattern.search(line):
                    finished = True
            state = "X" if error else ("N" if finished else "R") if conts is None else "D" if conts == [] else "C"
            if state == "C":
                for cont in conts:
                    size = len(cont)
                    vs = "\"" + "+".join(cont) + "\""
                    sum.write(f"{path},{state},{size},{vs}\n")
            else:
                size = -1 if conts is None else len(conts)
                vs = "-"
                sum.write(f"{path},{state},{size},{vs}\n")