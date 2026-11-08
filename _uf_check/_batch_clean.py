import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute("select axiom,state from axiom where user='py' and state in ('failed','plausible')")
print('bad', cur.fetchall())
for a in ['Matrix.Dot.eq.Expr.swap.left','Matrix.All_InDotSwapMatrix.of.Eq_SetOf_EqRange','Matrix.SetOfDotGetSwapMatrix.eq.Range','Matrix.AppendHstackS.eq.MatProd_SwapMatrix.of.Le','Matrix.AppendHstackS.eq.SwapMatrix','Matrix.Any_Eq_Dot_MatProd_SwapMatrix']:
  cur.execute("select axiom,state from axiom where user='py' and axiom=%s",(a,)); print(cur.fetchall())
conn.close()
