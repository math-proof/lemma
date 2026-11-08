import os, mysql.connector
user_col='py'
old='Finset.And.of.Eq_Adjoint.Imp_Gt_0.Eq_Ite.Cholesky'
new='Matrix.Eq_Mul_Adjoint.of.All_Eq_Lt.All_Lt0Dot_MulVec.EqAdjoint'
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password=os.environ.get('MYSQL_PWD','prod'), host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
def fetch(sql,p):
    cur.execute(sql,p); return cur.fetchall()
print('before old', fetch("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s",(user_col,old)))
print('before new', fetch("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s",(user_col,new)))
for sql,p in [
 ("delete from suggest where user=%s and prefix=%s and phrase=%s",(user_col,'Finset.And.of.Eq_Adjoint.Imp_Gt_0.Eq_Ite.','Cholesky')),
 ("delete from suggest where user=%s and prefix=%s and phrase=%s",(user_col,'Finset.And.of.Eq_Adjoint.Imp_Gt_0.Eq_Ite.Cholesky.','apply')),
]:
    cur.execute(sql,p); print('del',cur.rowcount)
cur.execute("""insert ignore into suggest (user,prefix,phrase,`usage`) values
 (%s,'Matrix.','Eq_Mul_Adjoint',1),
 (%s,'Matrix.Eq_Mul_Adjoint.','of',1),
 (%s,'Matrix.Eq_Mul_Adjoint.of.','All_Eq_Lt',1),
 (%s,'Matrix.Eq_Mul_Adjoint.of.All_Eq_Lt.','All_Lt0Dot_MulVec',1),
 (%s,'Matrix.Eq_Mul_Adjoint.of.All_Eq_Lt.All_Lt0Dot_MulVec.','EqAdjoint',1),
 (%s,'Matrix.Eq_Mul_Adjoint.of.All_Eq_Lt.All_Lt0Dot_MulVec.EqAdjoint.','apply',1)""", (user_col,)*6)
print('suggest',cur.rowcount)
for sql in [
 "update axiom set axiom=%s where user=%s and axiom=%s",
 "update hierarchy set caller=%s where user=%s and caller=%s",
 "update hierarchy set callee=%s where user=%s and callee=%s",
 "update `function` set caller=%s where user=%s and caller=%s",
 "update `function` set callee=%s where user=%s and callee=%s",
]:
    cur.execute(sql,(new,user_col,old)); print(sql.split()[1], cur.rowcount)
conn.commit()
print('after old', fetch("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s",(user_col,old)))
print('after new', fetch("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s",(user_col,new)))
# existence leaf untouched
print('existence', fetch("select axiom,state from axiom where user=%s and axiom=%s",(user_col,'Matrix.Any_And_Eq_Mul_Adjoint.of.All_Lt0Dot_MulVec.EqAdjoint')))
conn.close()
