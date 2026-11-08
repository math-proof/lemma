import os, mysql.connector
user_col='py'
old='Tensor.Stack.eq.Dot.swapn.helper'
new='Matrix.Stack.eq.Dot.swapn.helper'
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password=os.environ.get('MYSQL_PWD','prod'), host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
def fetch(sql,p=None):
    cur.execute(sql,p or ()); return cur.fetchall()
print('before', fetch("select axiom,state from axiom where user=%s and axiom in (%s,%s)",(user_col,old,new)))
# suggest deletes: Tensor.Stack.eq.Dot.swapn. / helper and apply
for sql,p in [
 ("delete from suggest where user=%s and prefix=%s and phrase=%s",(user_col,'Tensor.Stack.eq.Dot.swapn.','helper')),
 ("delete from suggest where user=%s and prefix=%s and phrase=%s",(user_col,'Tensor.Stack.eq.Dot.swapn.helper.','apply')),
]:
    cur.execute(sql,p); print('del',cur.rowcount)
cur.execute("""insert ignore into suggest (user,prefix,phrase,`usage`) values
 (%s,'Matrix.','Stack',1),
 (%s,'Matrix.Stack.','eq',1),
 (%s,'Matrix.Stack.eq.','Dot',1),
 (%s,'Matrix.Stack.eq.Dot.','swapn',1),
 (%s,'Matrix.Stack.eq.Dot.swapn.','helper',1),
 (%s,'Matrix.Stack.eq.Dot.swapn.helper.','apply',1)""", (user_col,)*6)
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
print('after', fetch("select axiom,state from axiom where user=%s and axiom in (%s,%s)",(user_col,old,new)))
conn.close()
import os
print('paths', os.path.exists(r'Lemma\Matrix\Stack\eq\Dot\swapn\helper.py'), os.path.exists(r'Lemma\Tensor\Stack\eq\Dot\swapn\helper.py'))
