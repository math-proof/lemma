import os, mysql.connector
user_col='py'
old='Tensor.AppendHstackS.eq.MatProd_SwapMatrix.of.Le'
new='Matrix.AppendHstackS.eq.MatProd_SwapMatrix.of.Le'
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password=os.environ.get('MYSQL_PWD','prod'), host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
def fetch(sql,p=None):
    cur.execute(sql,p or ()); return cur.fetchall()
print('before', fetch("select axiom,state from axiom where user=%s and axiom in (%s,%s)",(user_col,old,new)))
for sql,p in [
 ("delete from suggest where user=%s and prefix=%s and phrase=%s",(user_col,'Tensor.AppendHstackS.eq.MatProd_SwapMatrix.of.','Le')),
 ("delete from suggest where user=%s and prefix=%s and phrase=%s",(user_col,'Tensor.AppendHstackS.eq.MatProd_SwapMatrix.of.Le.','apply')),
]:
    cur.execute(sql,p); print('del',cur.rowcount)
cur.execute("""insert ignore into suggest (user,prefix,phrase,`usage`) values
 (%s,'Matrix.','AppendHstackS',1),
 (%s,'Matrix.AppendHstackS.','eq',1),
 (%s,'Matrix.AppendHstackS.eq.','MatProd_SwapMatrix',1),
 (%s,'Matrix.AppendHstackS.eq.MatProd_SwapMatrix.','of',1),
 (%s,'Matrix.AppendHstackS.eq.MatProd_SwapMatrix.of.','Le',1),
 (%s,'Matrix.AppendHstackS.eq.MatProd_SwapMatrix.of.Le.','apply',1)""", (user_col,)*6)
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
print('paths', __import__('os').path.exists(r'Lemma\Matrix\AppendHstackS\eq\MatProd_SwapMatrix\of\Le.py'), __import__('os').path.exists(r'Lemma\Tensor\AppendHstackS\eq\MatProd_SwapMatrix\of\Le.py'))
