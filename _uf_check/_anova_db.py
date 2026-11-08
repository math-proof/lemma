import os, mysql.connector
user_col='py'
old='Rat.Sum_SquareSub_DivSum.eq.AddMul_SumSquareSubDivSSum'
new='Finset.Sum_SquareSub_DivSum.eq.AddMul_Sum_SquareSubDivSSum'
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password=os.environ.get('MYSQL_PWD','prod'), host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
def fetch(sql,p=None):
    cur.execute(sql,p or ()); return cur.fetchall()
print('before old', fetch("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s",(user_col,old)))
print('before new', fetch("select axiom from axiom where user=%s and axiom=%s",(user_col,new)))
for sql,p in [
 ("delete from suggest where user=%s and prefix=%s and phrase=%s",(user_col,'Rat.Sum_SquareSub_DivSum.eq.','AddMul_SumSquareSubDivSSum')),
 ("delete from suggest where user=%s and prefix=%s and phrase=%s",(user_col,'Rat.Sum_SquareSub_DivSum.eq.AddMul_SumSquareSubDivSSum.','apply')),
]:
    cur.execute(sql,p); print('del',cur.rowcount)
cur.execute("""insert ignore into suggest (user,prefix,phrase,`usage`) values
 (%s,'Finset.','Sum_SquareSub_DivSum',1),
 (%s,'Finset.Sum_SquareSub_DivSum.','eq',1),
 (%s,'Finset.Sum_SquareSub_DivSum.eq.','AddMul_Sum_SquareSubDivSSum',1),
 (%s,'Finset.Sum_SquareSub_DivSum.eq.AddMul_Sum_SquareSubDivSSum.','apply',1)""", (user_col,)*4)
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
print('after old', fetch("select axiom from axiom where user=%s and axiom=%s",(user_col,old)))
print('after new', fetch("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s",(user_col,new)))
conn.close()
import os
print('paths', os.path.exists(r'Lemma\Finset\Sum_SquareSub_DivSum\eq\AddMul_Sum_SquareSubDivSSum.py'), os.path.exists(r'Lemma\Rat\Sum_SquareSub_DivSum\eq\AddMul_SumSquareSubDivSSum.py'))
