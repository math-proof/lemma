import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for a in ['Tensor.Dot.eq.Expr.swap.right','Matrix.Dot.eq.Expr.swap.right','Tensor.Dot.eq.Expr.swap','Tensor.Dot.eq.Expr']:
  cur.execute("select axiom,state from axiom where user='py' and axiom=%s",(a,)); print(a, cur.fetchall())
for pat in ['%Dot.eq.Expr.swap%','%Expr.swap.right%','%.swap.right']:
  cur.execute("select axiom,state from axiom where user='py' and axiom like %s",(pat,))
  rows=cur.fetchall()
  if rows: print(pat, rows[:30])
old='Tensor.Dot.eq.Expr.swap.right'
cur.execute("select caller from hierarchy where user='py' and callee=%s",(old,)); print('callee', cur.fetchall())
conn.close()
