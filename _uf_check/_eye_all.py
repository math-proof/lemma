import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute("select axiom,state from axiom where user='py' and axiom like %s",('%Eye%',))
for a,s in cur.fetchall():
  if 'Swap' in a or 'MatProd' in a or a.startswith('Tensor.') or a.startswith('Matrix.'):
    print(s, a)
conn.close()
