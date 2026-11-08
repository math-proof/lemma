import os, mysql.connector
conn = mysql.connector.connect(user=os.environ.get("USERNAME"), password="prod", host="localhost", database="axiom", charset="utf8mb4", auth_plugin="mysql_native_password")
cur = conn.cursor()
a = "Random.Eq.Lim.Prob.of.Eq_Conditioned.Eq_Expect.Eq_Var.law_of_large_numbers"
cur.execute("select axiom,state,lean,left(latex,500) from axiom where user=%s and axiom=%s", ("py", a))
print(cur.fetchone())
# lean side if any
for user in ["lean","lemma"]:
  cur.execute("select axiom,state,lean from axiom where user=%s and (axiom like %s or axiom like %s) order by axiom", (user, "%law_of_large%", "%Large%"))
  rows=cur.fetchall(); print("user", user, rows[:20])
conn.close()
