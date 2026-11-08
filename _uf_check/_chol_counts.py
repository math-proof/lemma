import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password=os.environ.get('MYSQL_PWD','prod'), host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute("select state, count(*) from axiom where user='py' group by state order by state")
print('states', cur.fetchall())
cur.execute("select count(*) from axiom where user='py' and state='proved'")
print('proved', cur.fetchall())
cur.execute("select axiom,state from axiom where user='py' and axiom in (%s,%s,%s)", (
 'Matrix.Eq_Mul_Adjoint.of.All_Eq_Lt.All_Lt0Dot_MulVec.EqAdjoint',
 'Matrix.Any_And_Eq_Mul_Adjoint.of.All_Lt0Dot_MulVec.EqAdjoint',
 'Matrix.EqMul_T_1.IsLowerTriangular.IsUpperTriangular.EqMulS'))
print('keys', cur.fetchall())
