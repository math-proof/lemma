from sympy import MySQL
from util.utility import user
inst = MySQL.instance()
for pat in ['%%DistributedAdd%%','%%Distributed.Add%%','%%Distributed_Gaussian%%','%%Eq_Conditioned%%Gaussian%%','%%gaussian%%Indep%%','%%Indep%%Gaussian%%']:
    rows = list(inst.query("select axiom, state from axiom.axiom where user='%s' and axiom like '%s'" % (user, pat)))
    if rows: print(pat, rows)
