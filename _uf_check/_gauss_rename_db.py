from sympy import MySQL
from util.utility import user
i = MySQL.instance()
old = 'Random.Distributed.Add.of.Eq_Conditioned.Distributed.Distributed.gaussian'
new = 'Random.DistributedAdd.of.Distributed_Gaussian.Distributed_Gaussian.Indep'
print('user', user)
print('before old', list(i.query("select axiom,state,length(ifnull(latex,'')) from axiom.axiom where user='%s' and axiom='%s'" % (user, old))))
print('before new', list(i.query("select axiom,state,length(ifnull(latex,'')) from axiom.axiom where user='%s' and axiom='%s'" % (user, new))))

stmts = [
  "delete from axiom.suggest where user = '%s' and prefix = 'Random.Distributed.Add.of.Eq_Conditioned.Distributed.Distributed.' and phrase = 'gaussian'" % user,
  "delete from axiom.suggest where user = '%s' and prefix = 'Random.Distributed.Add.of.Eq_Conditioned.Distributed.Distributed.gaussian.' and phrase = 'apply'" % user,
  """insert ignore into axiom.suggest (user, prefix, phrase, `usage`) values
    ('%s', 'Random.', 'DistributedAdd', 1),
    ('%s', 'Random.DistributedAdd.', 'of', 1),
    ('%s', 'Random.DistributedAdd.of.', 'Distributed_Gaussian', 1),
    ('%s', 'Random.DistributedAdd.of.Distributed_Gaussian.', 'Distributed_Gaussian', 1),
    ('%s', 'Random.DistributedAdd.of.Distributed_Gaussian.Distributed_Gaussian.', 'Indep', 1),
    ('%s', 'Random.DistributedAdd.of.Distributed_Gaussian.Distributed_Gaussian.Indep.', 'apply', 1)""" % (user,user,user,user,user,user),
  "update axiom.axiom set axiom = '%s' where user = '%s' and axiom = '%s'" % (new, user, old),
  "update axiom.hierarchy set caller = '%s' where user = '%s' and caller = '%s'" % (new, user, old),
  "update axiom.hierarchy set callee = '%s' where user = '%s' and callee = '%s'" % (new, user, old),
  "update axiom.`function` set caller = '%s' where user = '%s' and caller = '%s'" % (new, user, old),
  "update axiom.`function` set callee = '%s' where user = '%s' and callee = '%s'" % (new, user, old),
]
for s in stmts:
    try:
        i.execute(s)
        print('OK:', s[:120])
    except Exception as e:
        print('FAIL:', s[:120], '->', e)
i.commit()
print('after old', list(i.query("select axiom,state,length(ifnull(latex,'')) from axiom.axiom where user='%s' and axiom='%s'" % (user, old))))
print('after new', list(i.query("select axiom,state,length(ifnull(latex,'')) from axiom.axiom where user='%s' and axiom='%s'" % (user, new))))
print('suggest sample', list(i.query("select prefix,phrase from axiom.suggest where user='%s' and prefix like 'Random.DistributedAdd%%' limit 10" % user)))
