from pathlib import Path
import re
CREATE = re.compile(r'#\s*created on (\d{4}-\d{2}-\d{2})', re.I)
root = Path('Lemma')
n = 0
with open(r'E:\github\py\_py_created_dates.tsv', 'w', encoding='utf-8', newline='\n') as out:
    for p in root.rglob('*.py'):
        if p.name == '__init__.py' or p.name.endswith('.echo.py'):
            continue
        try:
            text = p.read_text(encoding='utf-8')
        except Exception as e:
            print('ERR', p, e)
            continue
        m = CREATE.search(text)
        if not m:
            continue
        mod = '.'.join(p.with_suffix('').relative_to(root).parts)
        out.write(f'{mod}\t{m.group(1)}\n')
        n += 1
print('wrote', n)
