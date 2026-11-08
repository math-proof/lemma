from sympy import MySQL
from util.utility import user
i = MySQL.instance()
old = 'Random.Distributed.Add.of.Eq_Conditioned.Distributed.Distributed.gaussian'
new = 'Random.DistributedAdd.of.Distributed_Gaussian.Distributed_Gaussian.Indep'
print('old', list(i.query("select axiom,state,length(ifnull(latex,'')) from axiom.axiom where user='%s' and axiom='%s'" % (user, old))))
print('new', list(i.query("select axiom,state,length(ifnull(latex,'')) from axiom.axiom where user='%s' and axiom='%s'" % (user, new))))
