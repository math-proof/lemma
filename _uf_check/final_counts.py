from sympy import MySQL
from util.utility import user
rows = list(MySQL.instance.query("select state, count(*) c from axiom where user='%s' group by state order by state" % user))
print('state_counts=', rows, flush=True)
total = list(MySQL.instance.query("select count(*) from axiom where user='%s'" % user))[0][0]
proved = list(MySQL.instance.query("select count(*) from axiom where user='%s' and state='proved'" % user))[0][0]
plausible = list(MySQL.instance.query("select count(*) from axiom where user='%s' and state='plausible'" % user))[0][0]
failed = list(MySQL.instance.query("select count(*) from axiom where user='%s' and state='failed'" % user))[0][0]
print('total=', total, 'proved=', proved, 'plausible=', plausible, 'failed=', failed, flush=True)
print('matrix=', list(MySQL.instance.query("select axiom, state, length(latex) from axiom where user='%s' and axiom='Matrix.DetBlock_Stack_MulPowS.eq.Mul_Prod_Factorial.of.All'" % user)), flush=True)
print('old_gone=', list(MySQL.instance.query("select axiom from axiom where user='%s' and axiom like 'Finset.DetBlock_Stack_MulPowS%%'" % user)), flush=True)
