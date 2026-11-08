import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password=os.environ.get('MYSQL_PWD','prod'), host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for pat in ['%ChiSquared%','%chi_squared%','%All_Distributed_Gaussian%','%Distributed.ChiSquared%','%Chi%Gaussian%Indep%']:
    cur.execute("select axiom, state from axiom where user='py' and axiom like %s", (pat,))
    rows=cur.fetchall()
    if rows:
        print(pat)
        for r in rows: print(' ', r)
conn.close()
