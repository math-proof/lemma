import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute("select axiom,state from axiom where user='py' and state in ('failed','plausible')")
print('bad', cur.fetchall())
conn.close()
