#
# source /Users/ericklavins/Courses/LeanW26/.venv/bin/activate
# python proof_state.py

import leanclient as lc

def log_proof_states(client, infile: str, outfile: str ):

    print(f". {infile}")
    
    sfc = client.create_file_client(infile)
    sfc.open_file()
    file_content = sfc.get_file_content()
    lines = file_content.split('\n')

    with open(outfile, "w") as f:
 
        for i, line in enumerate(lines):
            try:
                goal = sfc.get_goal(i, len(line))  # line number `i`, column at end of line
                if len(goal['goals']) > 0:
                    f.write(f"{line} <proofstate>{goal['goals']}</proofstate>\n")
                else:
                    f.write(f"{line}\n")
            except Exception as e:
                f.write(f"{line}\n")

    sfc.close_file()

print("Starting Client")
client = lc.LeanLSPClient("/Users/ericklavins/Courses/LeanW26")

print("Processing Files")
log_proof_states( client,  "LeanW26/Categories/BinaryProduct.lean", "bp.lean")
log_proof_states( client,  "LeanW26/Categories/Exponential.lean", "exp.lean")
log_proof_states( client,  "LeanW26/Introduction/Lean.lean", "lean.lean")

print("Closing client")
client.close()