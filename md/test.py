import subprocess

file = "Introduction/Lean"

cmd = 'python3 ./dm.py ' + 'src/' + file + '.log' + ' > ' + 'src/' + file + '.md'
print(cmd)
try:
  subprocess.run([cmd], shell=True)
except subprocess.CalledProcessError as e:
    print(f"Command failed with return code {e.returncode}")
    print(e.stderr)  