import leanclient as lc

# Start a new client, point it to your lean project root (where lakefile.toml is located).
PROJECT_PATH = "/Users/ericklavins/Courses/LeanW26/"
client = lc.LeanLSPClient(PROJECT_PATH,initial_build=False)

# Query a lean file in your project
file_path = "LeanW26/Tools/LCTest.lean"
result = client.get_goal(file_path, line=0, character=24)
print("goal",result)

sfc = client.create_file_client(file_path)
change = lc.DocumentContentChange(text="exact rfl", start=[0, 21], end=[0, 29])
sfc.update_file(changes=[change])

result = client.get_goal(file_path, line=1, character=7)
print("\ngoal",result)

result = client.get_hover(file_path, line=0, character=16)
print("\nhover",result)

lean_program = """
#eval 1 + 2
def invalid_code : Nat := "hello" -- This will cause a type error
#check Nat
"""

print("\ncontent before", sfc.get_file_content())

lines = sfc.get_file_content().splitlines()
end_line = len(lines) - 1
end_char = len(lines[-1]) if lines else 0

change = lc.DocumentContentChange(text=lean_program, start=[0, 0], end=[end_line, end_char])
sfc.update_file(changes=[change])

print("\ncontent after", sfc.get_file_content())

diagnostics = sfc.get_diagnostics()
for d in diagnostics:
    print("\n", d["message"])