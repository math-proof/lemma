from util.utility import user
try:
    from util.MySQL import instance
except Exception:
    from util import javaScript as MySQL
    instance = MySQL.instance
rows = list(instance.select("select state, count(*) c from axiom where user='%s' group by state order by state" % user))
total = list(instance.select("select count(*) c from axiom where user='%s'" % user))
print('user', user)
for r in rows:
    print(r)
print('total', total)
