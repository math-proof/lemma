import os, mysql.connector
conn = mysql.connector.connect(user=os.environ.get("USERNAME"), password="prod", host="localhost", database="axiom", charset="utf8mb4", auth_plugin="mysql_native_password")
cur = conn.cursor()
pats = ["%music%","%Music%","%note%","%Note%","%piano%","%Piano%","%tone%","%Tone%","%octave%","%Octave%","%pitch%","%Pitch%","%Hz%","%freq%","%Freq%","%harmonic%","%Harmonic%","%scale%","%Scale%","%temper%","%Temper%","%interval%","%Interval%","%semitone%","%Semitone%","%chord%","%Chord%"]
seen=set()
for pat in pats:
    cur.execute("select axiom,state from axiom where user=%s and axiom like %s order by axiom", ("py", pat))
    for a,s in cur.fetchall():
        if a not in seen:
            seen.add(a); print(a, s)
# latex search
cur.execute("select axiom,state from axiom where user=%s and (latex like %s or latex like %s or latex like %s or latex like %s) order by axiom", ("py","%music%","%piano%","%octave%","%semitone%"))
print("===latex===")
for r in cur.fetchall(): print(r)
conn.close()
