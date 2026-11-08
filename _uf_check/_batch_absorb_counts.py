import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute("select axiom,state from axiom where user='py' and state in ('failed','plausible')")
bad=cur.fetchall(); print('bad', bad)
for a in ['Matrix.Any_Eq_Dot_MatProd_SwapMatrix','Matrix.Stack.eq.Dot.swapn.helper','Matrix.EqDotDot_SwapMatrix','Matrix.Eq.Sum.Pow.of.Eq_Dot','Matrix.Eq.Cup.Finset.of.Eq_Dot','Tensor.All_InStack.of.All_InDotSwapMatrix']:
  cur.execute("select axiom,state from axiom where user='py' and axiom=%s",(a,)); print(cur.fetchall())
cur.execute("select state, count(*) from axiom where user='py' group by state order by state")
print('states', cur.fetchall())
open(r'_uf_check\_batch_absorb_done.txt','w',encoding='utf-8').write(repr(bad))
conn.close()
