import os, mysql.connector
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
for q in [
 "select axiom,state from axiom where user='py' and axiom like %s",
]:
  for pat in ['%SquareSub%','%DivSum_SumMul%','%Sum_SquareSub_DivSum%','%AddMul_Sum_SquareSub%','%Rat.Sum_Sum_SquareSub%','%Finset.Sum_SquareSub%']:
    cur.execute(q,(pat,))
    rows=cur.fetchall()
    if rows:
      print(pat, rows[:40])
conn.close()
