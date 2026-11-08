import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for a in ['Matrix.Dot.eq.Expr.swap.right','Tensor.Dot.eq.Expr.swap.right','Matrix.EqDotDot_SwapMatrix','Tensor.EqDotDot_SwapMatrix']:
  cur.execute("select axiom,state,length(ifnull(latex,'')) from axiom where user='py' and axiom=%s",(a,)); print(a, cur.fetchall())
old='Matrix.Dot.eq.Expr.swap.right'
cur.execute("select caller from hierarchy where user='py' and callee=%s",(old,)); print('callee of right', cur.fetchall())
cur.execute("select count(*) from hierarchy where user='py' and caller=%s",(old,)); print('as caller', cur.fetchall())
conn.close()
