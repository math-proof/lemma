import os, mysql.connector
conn = mysql.connector.connect(user=os.environ.get("USERNAME"), password="prod", host="localhost", database="axiom", charset="utf8mb4", auth_plugin="mysql_native_password")
cur = conn.cursor()
a = "Random.Eq.Lim.Prob.of.Eq_Conditioned.Eq_Expect.Eq_Var.law_of_large_numbers"
cur.execute("select axiom,state,lean from axiom where user=%s and axiom=%s", ("py", a))
row=cur.fetchone(); print("py row", row)
cur.execute("select axiom,state,user from axiom where axiom like %s or lean like %s", ("%law_of_large%", "%law_of_large%"))
print("any", cur.fetchall())
conn.close()
