import os, unicodedata, json, std
os.environ['MYSQL_DATABASE'] = 'axiom'
from py import MySQL

char2tex = {}

word2tex = {}

if not os.path.exists('json/abbreviations.json'):
    if py.is_Linux():
        print(os.popen('bash sh/unicode.sh').read())
    else:
        print(os.popen('powershell sh/unicode.ps1').read())

with open('json/extra_unicode.json', 'r', encoding='utf8') as f:
    extra_unicode = json.load(f)
with open('json/abbreviations.json', 'r', encoding='utf8') as f:
    abbreviations = json.load(f)

abbreviations |= extra_unicode
    
for latex, char in abbreviations.items():
    mapping = word2tex if len(char) > 1 else char2tex
    if char not in mapping:
        mapping[char] = []
    mapping[char].append(latex)

data = []
# Iterate over all possible Unicode code points (0 to 0x10FFFF)
for code_point in range(0x110000):
    try:
        # Get the character from the code point
        char = chr(code_point)
        # Get the name of the character
        name = unicodedata.name(char)
        # Print the code point and name
        data.append((
            # ("\\u{:04X}" if code_point < 0x10000 else "\\U{:08X}").format(code_point), 
            char,
            name,
            py.json_encode(char2tex[char]) if char in char2tex else None
        ))
    except ValueError:
        # Skip code points that don't have a name or character
        pass

for word, latex in word2tex.items():
    data.append((
        word,
        None,
        py.json_encode(latex)
    ))

[*check_if_table_exists] = MySQL.instance.query('show tables like "unicode"')
if not check_if_table_exists:
    MySQL.instance.execute(open('sql/create/unicode.sql', 'r').read())

rowcount = MySQL.instance.load_data('unicode', data)
print(f'{rowcount} rows loaded into table unicode')

rowcount = MySQL.instance.execute("update unicode set latex = NULL where latex like 'null'")
print(f'{rowcount} rows were updated')

rowcount = MySQL.instance.execute("update unicode set name = NULL where name like 'null'")
print(f'{rowcount} rows were updated')

[*data] = MySQL.instance.query(open('sql/select/unicode.sql', 'r').read())
for row in data:
    print(row, 'is duplicate')
else:
    print(f'no duplicate latex is found')
# https://gitcode.com/gh_mirrors/un/unicodeit/blob/main/unicodeit/data.py
# https://gitee.com/kktao/libtex2omml/blob/master/unimathsymbols.txt
# https://pylatexenc.readthedocs.io/en/latest/latexencode/#id1
# https://github.com/ViktorQvarfordt/unicode-latex/blob/07e197af90dd351b4347c72d12af177caae8c090/unicode-latex.json
# https://github.com/kmgb/LaTeX-Unicode-Map/blob/main/output/symbols.txt
# https://www.johndcook.com/data.js
# https://www.w3.org/Math/characters/unicode.xml
# https://milde.users.sourceforge.net/LUCR/Math/data/unimathsymbols.txt
# https://github.com/jgm/texmath/blob/master/lib/totexmath/unimathsymbols.txt
# https://github.com/kawabata/math-symbols/blob/master/unimathsymbols.txt