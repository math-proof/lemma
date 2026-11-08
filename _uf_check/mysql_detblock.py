print('start', flush=True)
from sympy import MySQL
print('MySQL imported', flush=True)
from util.utility import user
print('user=', user, flush=True)
sql = "select axiom, state, length(latex) as llen from axiom where user='%s' and axiom like '%%DetBlock_Stack_MulPowS%%'" % user
rows = list(MySQL.instance.query(sql))
print('rows=', rows, flush=True)
sql2 = "select state, count(*) from axiom where user='%s' group by state" % user
print('counts=', list(MySQL.instance.query(sql2)), flush=True)
