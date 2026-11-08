import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for a in ['Tensor.EqDotDot_SwapMatrix','Matrix.EqDotDot_SwapMatrix','Tensor.MatProd.eq.Eye','Tensor.SwapMatrix.eq.Eye','Matrix.Any_Eq_Dot_MatProd_SwapMatrix','Matrix.Stack.eq.Dot.swapn.helper']:
  cur.execute("select axiom,state from axiom where user='py' and axiom=%s",(a,)); print(a, cur.fetchall())
old='Tensor.EqDotDot_SwapMatrix'
cur.execute("select caller from hierarchy where user='py' and callee=%s",(old,)); print('callee', cur.fetchall())
cur.execute("select count(*) from hierarchy where user='py' and caller=%s",(old,)); print('as caller', cur.fetchall())
cur.execute("select axiom from axiom where user='py' and axiom like %s",('%EqDotDot%',)); print('EqDotDot*', cur.fetchall())
conn.close()
