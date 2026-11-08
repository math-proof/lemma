import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='mysql', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute('show databases')
dbs=[r[0] for r in cur.fetchall()]
print(dbs)
for db in dbs:
  if db in ('information_schema','performance_schema','mysql','sys'): continue
  try:
    cur.execute(f"show tables from `{db}`")
    tables=[t[0] for t in cur.fetchall()]
    if any('axiom' in t or 'lemma' in t or 'lean' in t for t in tables):
      print(db, tables[:30])
  except Exception as e:
    print(db, e)
conn.close()
