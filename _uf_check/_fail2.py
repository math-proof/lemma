import os, mysql.connector, json
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute("show tables")
tables=[r[0] for r in cur.fetchall()]
print('tables with err/fail/log', [t for t in tables if any(x in t.lower() for x in ('err','fail','log','trace','prove'))])
for t in tables:
  if 'err' in t.lower() or t in ('traceback','exception','failure'):
    cur.execute(f"desc `{t}`")
    print(t, cur.fetchall())
cur.execute("select state, latex from axiom where user='py' and axiom=%s",('Matrix.Any_Eq_Dot_MatProd_SwapMatrix',))
row=cur.fetchone()
print('state', row[0], 'latex_tail', (row[1] or b'')[-800:] if isinstance(row[1], (bytes,bytearray)) else str(row[1])[-800:])
conn.close()
