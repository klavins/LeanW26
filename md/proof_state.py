#
# source /Users/ericklavins/Courses/LeanW26/.venv/bin/activate
# python3 proof_state.py
#

import subprocess
import re
import leanclient as lc

def log_proof_states(client, infile: str, outfile: str ):

    print(f". {infile}")
    
    sfc = client.create_file_client(infile)
    sfc.open_file()
    file_content = sfc.get_file_content()
    lines = file_content.split('\n')

    with open(outfile, "w") as f:

        r = sfc.get_diagnostics()
 
        for i, line in enumerate(lines):

            try:
                goal = sfc.get_goal(i, len(line))  # line number `i`, column at end of line
                if goal and len(goal['goals']) > 0:
                  f.write(f"{line} <proofstate>{goal['goals']}</proofstate>\n")
                else:
                  f.write(f"{line}\n")                      

            except Exception as e:
                print(e)
                f.write(f"{line}\n")

    sfc.close_file()

root = "/Users/ericklavins/Courses/LeanW26"
print("Starting Client")
client = lc.LeanLSPClient(root)

files = [

   "Introduction/Lean"
#   "Introduction/Programming",
#   "Introduction/Datatypes",

#   "TypeTheory/Overview",
#   "TypeTheory/LambdaCalculus",
#   "TypeTheory/Universes",
#   "TypeTheory/Simple",
#   "TypeTheory/NonSimpleTypes",
#   "TypeTheory/Inference",

 # "Logic/Connectives"

]

print("Processing Files")

for file in files :

  infile  = "LeanW26/" + file + ".lean"
  logfile = "src/" + file + ".log"
  mdfile  = 'src/' + file + '.md'

  log_proof_states( client,  infile, logfile)

  cmd = 'python3 ./dm.py ' + logfile + ' > ' + mdfile
  subprocess.run([cmd], shell=True)

print("Closing client")
client.close()