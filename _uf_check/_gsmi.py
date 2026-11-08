import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for a in ['Tensor.GetSwapMatrix.eq.Ite','Matrix.GetSwapMatrix.eq.Ite','GetSwapMatrix.eq.Ite']:
  cur.execute("select axiom,state,is_generated from axiom where user='py' and axiom=%s",(a,)); print('exact',a,cur.fetchall())
cur.execute("select axiom,state from axiom where user='py' and axiom like '%GetSwapMatrix%Ite%'")
print('like',cur.fetchall())
cur.execute("select axiom,state from axiom where user='py' and axiom like '%GetSwapMatrix%'")
print('all GetSwap',cur.fetchall())
conn.close()
