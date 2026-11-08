import os, mysql.connector
user_col = 'py'
old = 'Random.Distributed.Add.of.Eq_Conditioned.Distributed.Distributed.gaussian'
new = 'Random.DistributedAdd.of.Distributed_Gaussian.Distributed_Gaussian.Indep'
conn = mysql.connector.connect(
    user=os.environ.get('USERNAME') if os.name=='nt' else os.environ.get('USER'),
    password=os.environ.get('MYSQL_PWD'),
    host=os.environ.get('MYSQL_HOST','127.0.0.1'),
    database='axiom',
    charset='utf8mb4',
    auth_plugin='mysql_native_password',
)
cur = conn.cursor()
def q(sql, params=None):
    cur.execute(sql, params or ())
    try: return cur.fetchall()
    except: return []
print('before old', q("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s", (user_col, old)))
print('before new', q("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s", (user_col, new)))
stmts = [
  ("delete from suggest where user=%s and prefix=%s and phrase=%s", (user_col, 'Random.Distributed.Add.of.Eq_Conditioned.Distributed.Distributed.', 'gaussian')),
  ("delete from suggest where user=%s and prefix=%s and phrase=%s", (user_col, 'Random.Distributed.Add.of.Eq_Conditioned.Distributed.Distributed.gaussian.', 'apply')),
]
for sql,p in stmts:
    cur.execute(sql,p); print('OK delete', cur.rowcount)
cur.execute("""insert ignore into suggest (user, prefix, phrase, `usage`) values
 (%s,'Random.','DistributedAdd',1),
 (%s,'Random.DistributedAdd.','of',1),
 (%s,'Random.DistributedAdd.of.','Distributed_Gaussian',1),
 (%s,'Random.DistributedAdd.of.Distributed_Gaussian.','Distributed_Gaussian',1),
 (%s,'Random.DistributedAdd.of.Distributed_Gaussian.Distributed_Gaussian.','Indep',1),
 (%s,'Random.DistributedAdd.of.Distributed_Gaussian.Distributed_Gaussian.Indep.','apply',1)""",
 (user_col,)*6)
print('OK suggest insert', cur.rowcount)
for sql in [
  "update axiom set axiom=%s where user=%s and axiom=%s",
  "update hierarchy set caller=%s where user=%s and caller=%s",
  "update hierarchy set callee=%s where user=%s and callee=%s",
  "update `function` set caller=%s where user=%s and caller=%s",
  "update `function` set callee=%s where user=%s and callee=%s",
]:
    cur.execute(sql, (new, user_col, old)); print('OK', sql.split()[1], cur.rowcount)
conn.commit()
print('after old', q("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s", (user_col, old)))
print('after new', q("select axiom,state,length(ifnull(latex,'')) from axiom where user=%s and axiom=%s", (user_col, new)))
cur.close(); conn.close()
