from sympy import MySQL
from util.utility import user
inst = MySQL.instance()
rows = list(inst.query("select state, count(*) as c from axiom.axiom where user='%s' group by state order by state" % user))
print('state counts:', rows)
rows2 = list(inst.query("select axiom, state from axiom.axiom where user='%s' and axiom like '%%EqMul_T_1%%'" % user))
print('EqMul_T_1:', rows2)
rows3 = list(inst.query("select axiom, state from axiom.axiom where user='%s' and axiom like '%%MulTEq1%%'" % user))
print('old MulTEq1:', rows3)
