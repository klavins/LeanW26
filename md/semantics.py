#
# source /Users/ericklavins/Courses/LeanW26/.venv/bin/activate
# python3 semantics.py
#

import subprocess
import re
import leanclient as lc

def log_proof_states(client, infile: str, outfile: str ):

    print(f"  -> {infile}")    
    sfc = client.create_file_client(infile)
    sfc.open_file()
    file_content = sfc.get_file_content()
    lines = file_content.split('\n')

    with open(outfile, "w") as f:
      sfc.get_diagnostics()
      tokens = sfc.get_semantic_tokens()
      print(len(tokens))
      for t in tokens:
        print(t)

    sfc.close_file()

# Main Entry Point


root = "/Users/ericklavins/Courses/LeanW26"
print("Starting Client")
client = lc.LeanLSPClient(root)

files = [

#   "Introduction/Lean"
# "Introduction/Programming"
#   "Introduction/Datatypes",

#   "TypeTheory/Overview",
#   "TypeTheory/LambdaCalculus",
#   "TypeTheory/Universes",
#   "TypeTheory/Simple",
   "TypeTheory/NonSimpleTypes"
#   "TypeTheory/Inference",

]

print("Processing Files")

for file in files : 
  log_proof_states(
      client,  
      "LeanW26/" + file + ".lean", 
      "src/" + file + ".log")

print("Closing client")
client.close()