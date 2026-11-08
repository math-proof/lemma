import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for pat in ['%EqT%Swap%','%SwapMatrix.eq.T%','%eq.Transpose%Swap%','%SwapMatrix%eq%T%','Tensor.EqT%','Matrix.EqT%']:
  cur.execute("select axiom,state from axiom where user='py' and axiom like %s",(pat,))
  rows=cur.fetchall()
  if rows: print(pat, rows[:20])
cur.execute("select axiom from axiom where user='py' and (axiom like '%SwapMatrix%' and (axiom like '%T%' or axiom like '%Transpose%' or axiom like '%sym%'))")
print('swap+T', cur.fetchall())
conn.close()
