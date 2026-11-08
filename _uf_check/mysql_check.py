from util.MySQL import instance
from util.utility import user
q1 = "select axiom, state, lapse from axiom where user='%s' and axiom like '%%DetBlock_Stack_MulPowS%%'" % user
print('DetBlock rows:', list(instance.select(q1)))
q2 = "select state, count(*) c from axiom where user='%s' group by state order by state" % user
print('state counts:', list(instance.select(q2)))
q3 = "select count(*) c from axiom where user='%s'" % user
print('total:', list(instance.select(q3)))
