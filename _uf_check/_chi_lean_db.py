import os, mysql.connector, re
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
# lean user?
cur.execute("select distinct user from axiom limit 20")
print('users', cur.fetchall())
for u in ['lean','py','cosmos']:
  cur.execute("select axiom,state,left(ifnull(latex,''),200) from axiom where user=%s and axiom like %s", (u, '%ChiSquared%'))
  rows=cur.fetchall()
  if rows:
    print('user', u)
    for r in rows: print(r)
cur.execute("select axiom,state,left(ifnull(latex,''),400), left(ifnull(lean,''),400) from axiom where axiom like %s", ('%All_Distributed_Gaussian.All_Indep%',))
print('All_Indep any user', cur.fetchall())
cur.execute("select axiom,user,state,left(ifnull(latex,''),500) from axiom where axiom like %s", ('%ChiSquared.of.Eq_Conditioned%',))
print('Eq_Conditioned', cur.fetchall())
conn.close()
