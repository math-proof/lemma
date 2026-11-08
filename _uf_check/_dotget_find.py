import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for a in ['Tensor.DotGetSwapMatrix.eq.Get','Matrix.DotGetSwapMatrix.eq.Get','Tensor.GetDot_SwapMatrix.eq.Get']:
  cur.execute("select axiom,state from axiom where user='py' and axiom=%s",(a,)); print(a, cur.fetchall())
old='Tensor.DotGetSwapMatrix.eq.Get'
cur.execute("select caller from hierarchy where user='py' and callee=%s",(old,)); print('callee', cur.fetchall())
cur.execute("select count(*) from hierarchy where user='py' and caller=%s",(old,)); print('as caller', cur.fetchall())
for pat in ['%DotGetSwapMatrix%','%GetDot_SwapMatrix%']:
  cur.execute("select axiom,state from axiom where user='py' and axiom like %s",(pat,)); print(pat, cur.fetchall())
conn.close()
