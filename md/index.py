import sys
import re

f = open(sys.argv[1], "r", encoding='utf-8')
md_file_name = sys.argv[1].split("../LeanBook/Chapters/")[1]
md_file_name = "./" + md_file_name.replace(".lean", ".md")

data = f.read()
lines = data.splitlines()

for line in lines:
    if line.startswith("def"):
        name = line.split(" ")[1]
        if len(name) > 1:
            print(f"- [{name}]({md_file_name}) (Definition)")

    if line.startswith("inductive"):
        name = line.split(" ")[1]
        print(f"- [{name}]({md_file_name}) (Inductive Type)")        