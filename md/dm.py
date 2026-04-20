import sys
import re
import html

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

comment_pattern = r'(?s:/-.*?-/)'

if "--notdone" in data:
    data = """
/-
<div class='uc'><span class='def'>def</span> <span class='slidedeck'>SlideDeck</span> <span class='eq'>:=</span> <span class='sorry'>sorry</span></div>
===
-/


"""

def offset_to_line_col(data, offset):
    """Convert character offset to 1-based line and column."""
    line = data[:offset].count('\n') + 1
    last_newline = data.rfind('\n', 0, offset)
    if last_newline == -1:
        col = offset + 1
    else:
        col = offset - last_newline
    return line, col

def find_stripped_range(data, start, end):
    """Find the line range of stripped code within data[start:end]."""
    segment = data[start:end]
    stripped = segment.strip()
    if not stripped:
        return None, None, None, None
    # Find where stripped content starts/ends in original
    lstrip_count = len(segment) - len(segment.lstrip())
    rstrip_count = len(segment) - len(segment.rstrip())
    actual_start = start + lstrip_count
    actual_end = end - rstrip_count
    start_line, start_col = offset_to_line_col(data, actual_start)
    end_line, end_col = offset_to_line_col(data, actual_end)
    return stripped, start_line, start_col, end_line

def output_code_block(code, start_line, end_line):
    """Output a Lean code block with position data attributes."""
    # Escape HTML but preserve the exact content without extra newlines
    escaped = html.escape(code)
    # Use a div wrapper to prevent showdown from modifying the structure
    # Put on its own line for readability in the markdown, but no newlines inside <code>
    print()  # blank line before for markdown parsing
    print(f'<div class="lean-code" data-start-line="{start_line}" data-end-line="{end_line}"><pre><code>{escaped}</code></pre></div>')
    print()  # blank line after

# Process file using finditer to preserve positions
last_end = 0
first_comment = True
for match in re.finditer(comment_pattern, data):
    # Code before this comment (skip code before the first comment - it's usually imports/copyright)
    if match.start() > last_end and not first_comment:
        code, start_line, start_col, end_line = find_stripped_range(data, last_end, match.start())
        if code:
            output_code_block(code, start_line, end_line)

    first_comment = False

    # The comment itself (markdown content)
    comment_text = match.group(0)[2:-2]  # strip /- and -/
    print(comment_text)

    last_end = match.end()

# Code after last comment
if last_end < len(data):
    code, start_line, start_col, end_line = find_stripped_range(data, last_end, len(data))
    if code:
        output_code_block(code, start_line, end_line)

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

