import os, mysql.connector
conn = mysql.connector.connect(user=os.environ.get("USERNAME"), password="prod", host="localhost", database="axiom", charset="utf8mb4", auth_plugin="mysql_native_password")
cur = conn.cursor()
pats = ["%Large%", "%WLLN%", "%SLLN%", "%LLN%", "%LawOf%", "%law_of%", "%SampleMean%", "%Mean_Sum%", "%Avg%", "%Chebyshev%", "%Bernoulli%"]
for pat in pats:
    cur.execute("select axiom,state from axiom where user=%s and axiom like %s order by axiom", ("py", pat))
    rows = cur.fetchall()
    if rows:
        print("===", pat, len(rows))
        for a,s in rows[:100]:
            print(a, s)
# also latex/html comment search if columns exist
try:
    cur.execute("show columns from axiom")
    cols=[r[0] for r in cur.fetchall()]; print("COLS", cols)
except Exception as e:
    print("cols err", e)
conn.close()
