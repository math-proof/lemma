import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute("select axiom,state from axiom where user='py' and axiom like '%GetSwapMatrix%'")
print('all GetSwap', cur.fetchall())
cur.execute("show columns from axiom")
print([r[0] for r in cur.fetchall()])
conn.close()
