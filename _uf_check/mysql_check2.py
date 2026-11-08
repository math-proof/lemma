from sympy import MySQL
from util.utility import user
print('user=', user, flush=True)
# describe axiom table
print('desc:', list(MySQL.instance.query('desc axiom')), flush=True)
sql = "select axiom, state, length(latex) llen from axiom where user='%s' and axiom like '%%DetBlock_Stack_MulPowS%%'" % user
print('rows:', list(MySQL.instance.query(sql)), flush=True)
new = "Matrix.DetBlock_Stack_MulPowS.eq.Mul_Prod_Factorial.of.All"
rows = list(MySQL.instance.query("select state, length(ifnull(latex,'')), left(ifnull(latex,''),120) from axiom where user='%s' and axiom='%s'" % (user, new)))
print('new:', rows, flush=True)
old = "Finset.DetBlock_Stack_MulPowS.eq.Mul_Prod_Factorial.vandermonde"
print('old:', list(MySQL.instance.query("select state, length(ifnull(latex,'')) from axiom where user='%s' and axiom='%s'" % (user, old))), flush=True)
