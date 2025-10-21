import os, unicodedata, json, std
os.environ['MYSQL_DATABASE'] = 'axiom'
from std import MySQL
from std.file import Text
from collections import defaultdict

sum = 0
err = 0
seen = defaultdict(list)
for line in Text('json/mathlib.jsonl'):
    obj = json.loads(line)
    name = obj['name']
    sum += 1
    name_lower = name.lower()
    if name_lower in seen:
        print(f'duplicate: {name}, old list : {seen[name_lower]}')
        seen[name_lower].append(name)
        continue
    seen[name_lower].append(name)
    [[count]] = MySQL.instance.query(f'select count(*) from mathlib where name = "{name}"')
    if count :
        continue
    print(name)
    err += 1
    # for MySQL.instance.select('mathlib')

print(f'finished, sum = {sum}')
print(f'new entries = {err}')