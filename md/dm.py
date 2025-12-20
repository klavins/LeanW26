import sys
import re

#
# Converts to lean to markdown by converting comment blocks to markdown and code to markdown code blocks. 
# 
# Usage:
#  
#   python3 dm.py my_lean_file.lean > my_lean_file.md
#
# The resulting markdown file can be viewed with your favorite viewer.
#

f = open(sys.argv[1], "r", encoding='utf-8')

data = f.read()

comment = r'(?s:(/-.*?-/))'

if "--notdone" in data:
    data = """
/-
Under Construction
===
-/

def SlideDeck := sorry
"""

for str in re.split(comment, data)[1:]:
    if len(str) > 1 and str[0] == '/' and str[1] == '-':
        markdown = str[2:len(str)-2]
        print(markdown)
    else:
        code = str.lstrip().rstrip()
        if len(code) > 0:
            print("```lean")   # there is no lean highlighter with my chrome plugin
            print(code)
            print('```')

copyright = """
License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   
"""

print(copyright)

