import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for pat in ['%.eq.Eye','%MatProd%Eye%','%Eye%MatProd%','Tensor.MatProd%','Matrix.MatProd%']:
  cur.execute("select axiom,state from axiom where user='py' and axiom like %s",(pat,))
  rows=cur.fetchall()
  if rows: print(pat, rows[:30])
conn.close()
