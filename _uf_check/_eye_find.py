import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for a in ['Tensor.MatProd.eq.Eye','Matrix.MatProd.eq.Eye','Tensor.Any_Eq_Dot_MatProd_SwapMatrix','Matrix.Any_Eq_Dot_MatProd_SwapMatrix']:
  cur.execute("select axiom,state from axiom where user='py' and axiom=%s",(a,)); print(a, cur.fetchall())
old='Tensor.MatProd.eq.Eye'
cur.execute("select caller from hierarchy where user='py' and callee=%s",(old,)); print('Eye hier callee', cur.fetchall())
cur.execute("select count(*) from hierarchy where user='py' and caller=%s",(old,)); print('Eye hier caller count', cur.fetchall())
conn.close()
