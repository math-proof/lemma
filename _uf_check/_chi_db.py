import os, mysql.connector
user_col='py'
old='Random.Distributed.ChiSquared.of.Eq_Conditioned.Distributed'
new='Random.Distributed.ChiSquared.of.All_Distributed_Gaussian.All_Indep'
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password=os.environ.get('MYSQL_PWD','prod'), host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
def fetch(sql,p=None):
    cur.execute(sql,p or ()); return cur.fetchall()
print('before old', fetch("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s",(user_col,old)))
print('before new', fetch("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s",(user_col,new)))
# also update any callers that still cite old path in .py
cur.execute("select distinct caller from hierarchy where user=%s and callee=%s",(user_col,old))
callers=[r[0] for r in cur.fetchall()]
cur.execute("select distinct caller from `function` where user=%s and callee=%s",(user_col,old))
callers=sorted(set(callers+[r[0] for r in cur.fetchall()]))
print('callers', callers)
for sql,p in [
 ("delete from suggest where user=%s and prefix=%s and phrase=%s",(user_col,'Random.Distributed.ChiSquared.of.Eq_Conditioned.','Distributed')),
 ("delete from suggest where user=%s and prefix=%s and phrase=%s",(user_col,'Random.Distributed.ChiSquared.of.Eq_Conditioned.Distributed.','apply')),
]:
    cur.execute(sql,p); print('del',cur.rowcount)
cur.execute("""insert ignore into suggest (user,prefix,phrase,`usage`) values
 (%s,'Random.','Distributed',1),
 (%s,'Random.Distributed.','ChiSquared',1),
 (%s,'Random.Distributed.ChiSquared.','of',1),
 (%s,'Random.Distributed.ChiSquared.of.','All_Distributed_Gaussian',1),
 (%s,'Random.Distributed.ChiSquared.of.All_Distributed_Gaussian.','All_Indep',1),
 (%s,'Random.Distributed.ChiSquared.of.All_Distributed_Gaussian.All_Indep.','apply',1)""", (user_col,)*6)
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
print('after old', fetch("select axiom,state from axiom where user=%s and axiom=%s",(user_col,old)))
print('after new', fetch("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s",(user_col,new)))
conn.close()
print('paths', __import__('os').path.exists(r'Lemma\Random\Distributed\ChiSquared\of\All_Distributed_Gaussian\All_Indep.py'), __import__('os').path.exists(r'Lemma\Random\Distributed\ChiSquared\of\Eq_Conditioned\Distributed.py'))
