import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute("select state, length(ifnull(latex,'')), left(ifnull(latex,''),500) from axiom where user='py' and axiom=%s",('Matrix.Any_Eq_Dot_MatProd_SwapMatrix',))
print(cur.fetchone())
# also check prove error tables if any
for t in ['error','prove','debug']:
  try:
    cur.execute(f"show tables like '{t}'")
    if cur.fetchone():
      cur.execute(f"select * from `{t}` where axiom like %s limit 3",('%Any_Eq_Dot_MatProd_SwapMatrix%',))
      print(t, cur.fetchall()[:2])
  except Exception as e:
    print(t, e)
conn.close()
