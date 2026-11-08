import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for a in ['Tensor.SwapMatrix.eq.Eye','Matrix.SwapMatrix.eq.Eye','Tensor.MatProd.eq.Eye','Matrix.MatProd.eq.Eye','Matrix.Any_Eq_Dot_MatProd_SwapMatrix','Tensor.Any_Eq_Dot_MatProd_SwapMatrix']:
  cur.execute("select axiom,state from axiom where user='py' and axiom=%s",(a,)); print(a, cur.fetchall())
old='Tensor.SwapMatrix.eq.Eye'
cur.execute("select caller from hierarchy where user='py' and callee=%s",(old,)); print('callee callers', cur.fetchall())
cur.execute("select count(*) from hierarchy where user='py' and caller=%s",(old,)); print('as caller', cur.fetchall())
cur.execute("select axiom from axiom where user='py' and axiom like %s",('%SwapMatrix.eq%',)); print('SwapMatrix.eq*', cur.fetchall())
cur.execute("select axiom from axiom where user='py' and axiom like %s",('%SwapMatrix%',)); 
rows=[r[0] for r in cur.fetchall() if 'Eye' in r[0] or 'SwapMatrix.eq' in r[0]]; print('eyeish', rows)
conn.close()
