from sympy import MySQL
from util.utility import user
print('user=', user, flush=True)
sql = "select axiom, state, length(latex) llen, length(python) plen from axiom where user='%s' and axiom like '%%DetBlock_Stack_MulPowS%%'" % user
rows = list(MySQL.instance.query(sql))
print('before delete:', rows, flush=True)
old = "Finset.DetBlock_Stack_MulPowS.eq.Mul_Prod_Factorial.vandermonde"
n = MySQL.instance.execute("delete from axiom where user='%s' and axiom='%s'" % (user, old))
print('deleted old rows:', n, flush=True)
rows = list(MySQL.instance.query(sql))
print('after delete:', rows, flush=True)
# also fetch latex head for new
new = "Matrix.DetBlock_Stack_MulPowS.eq.Mul_Prod_Factorial.of.All"
rows2 = list(MySQL.instance.query("select state, length(latex), left(latex,80) from axiom where user='%s' and axiom='%s'" % (user, new)))
print('new axiom:', rows2, flush=True)
