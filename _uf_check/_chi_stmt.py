import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute("select latex, lean from axiom where user='py' and axiom=%s", ('Random.Distributed.ChiSquared.of.Eq_Conditioned.Distributed',))
latex, lean = cur.fetchone()
if isinstance(latex, (bytes, bytearray)): latex = latex.decode('utf-8', errors='replace')
if isinstance(lean, (bytes, bytearray)): lean = lean.decode('utf-8', errors='replace') if lean else ''
print('=== PY LATEX ===')
print(latex[:3000] if latex else None)
print('=== PY LEAN COL ===')
print((lean or '')[:2000])
# list databases
cur.execute('show databases')
print('DBs', cur.fetchall())
conn.close()
