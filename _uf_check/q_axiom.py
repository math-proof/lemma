from util import javaScript as MySQL
from util.utility import user
inst = MySQL.instance
for row in inst.select("select axiom, state, left(latex,80) from axiom where user='%s' and axiom like '%%DetBlock_Stack_MulPowS%%'" % user):
    print(row)
print('--- proved count ---')
print(list(inst.select("select state, count(*) from axiom where user='%s' group by state" % user)))
