import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for pat in ['%Any_Eq_Dot_MatProd_SwapMatrix%','%SwapMatrix%']:
  cur.execute("select axiom,state from axiom where user='py' and axiom like %s",(pat,))
  rows=cur.fetchall();
  if rows: print(pat, rows)
old='Tensor.Any_Eq_Dot_MatProd_SwapMatrix'
cur.execute("select caller from hierarchy where user='py' and callee=%s",(old,)); print('hier callee', cur.fetchall())
cur.execute("select caller from hierarchy where user='py' and caller=%s",(old,)); print('hier caller', cur.fetchall()[:20], 'count', cur.rowcount)
cur.execute("select caller,callee from `function` where user='py' and (caller=%s or callee=%s)",(old,old)); print('func', cur.fetchall())
conn.close()
