from pathlib import Path
text = Path(r'Lemma/Rat/And/Eq/of/And/And/just_intonation.py').read_text(encoding='utf-8')
import re
for m in re.finditer(r'Symbol\((?:r)?"([^"]+)"', text):
    print(repr(m.group(1)))
# also plain Symbol(nu_1 without latex
for m in re.finditer(r'(\w+)\s*=\s*Symbol\(', text):
    print('bind', m.group(1))
