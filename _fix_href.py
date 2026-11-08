from pathlib import Path
import re

files = [
    Path(r'E:/github/py/static/components/render.vue'),
    Path(r'E:/github/py/target/vue/render.vue'),
]
# Match the broken lookbehind/lookahead that over-constrains In/Is
old_re = re.compile(
    r"search = search\.replace\(/\(\?<=\[\./\\\]\[A-Z\]\\w\*\[\./\\\]\)\(In\|Is\)\(\?=\[\./\\\]\[A-Z\]\)/g, m => m\.toLowerCase\(\)\);"
)
# Actually read file and find line containing (In|Is)
new_line = "                search = search.replace(/(?<=[.\/\\])(In|Is)(?=[.\/\\])/g, m => m.toLowerCase());"

for f in files:
    text = f.read_text(encoding='utf-8')
    lines = text.splitlines(keepends=True)
    changed = False
    out = []
    for line in lines:
        if '(In|Is)' in line and 'toLowerCase' in line and 'search.replace' in line:
            # preserve indent
            indent = line[:len(line) - len(line.lstrip(' '))]
            nl = indent + "search = search.replace(/(?<=[.\/\\])(In|Is)(?=[.\/\\])/g, m => m.toLowerCase());\n"
            # fix: in Python string for the vue source we need the same escapes as JS source
            nl = indent + 'search = search.replace(/(?<=[./\\])(In|Is)(?=[./\\])/g, m => m.toLowerCase());\n'
            # Wait - in the file the JS is: /(?<=[.\/\])(In|Is)(?=[.\/\])/g
            # Written as characters: (?<=[./\]) with backslash-backslash in some views
            pass
