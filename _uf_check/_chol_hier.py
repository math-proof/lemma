import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password=os.environ.get('MYSQL_PWD','prod'), host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for a in ['Finset.Any.And.of.Eq_Adjoint.Imp_Gt_0.Cholesky','Random.And.Ge.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Eq_Expect.Ge.drift']:
    cur.execute("select callee from hierarchy where user='py' and caller=%s limit 20", (a,))
    print(a, 'callees', cur.fetchall())
    cur.execute("select latex is not null, length(ifnull(latex,'')) from axiom where user='py' and axiom=%s", (a,))
    print(' latex', cur.fetchall())
conn.close()
