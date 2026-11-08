import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for pat in ['%GetDot%','%Get%SwapMatrix%','%SwapMatrix.eq.Get%','%.eq.Get']:
  cur.execute("select axiom,state from axiom where user='py' and axiom like %s",(pat,))
  rows=[r for r in cur.fetchall() if 'Swap' in r[0] or 'GetDot' in r[0] or r[0].endswith('.eq.Get')]
  if rows: print(pat, rows[:40])
# also any Tensor Get with Swap
cur.execute("select axiom from axiom where user='py' and axiom like 'Tensor.%' and axiom like '%SwapMatrix%'")
print('Tensor*SwapMatrix', [r[0] for r in cur.fetchall()])
conn.close()
