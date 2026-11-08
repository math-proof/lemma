import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password=os.environ.get('MYSQL_PWD','prod'), host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute("select axiom, state, lapse from axiom where user='py' and state='failed'")
print('failed', cur.fetchall())
conn.close()
