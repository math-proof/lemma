import os, mysql.connector
old='Rat.Sum_SquareSub_DivSum.eq.AddMul_SumSquareSubDivSSum'
new='Finset.Sum_SquareSub_DivSum.eq.AddMul_Sum_SquareSubDivSSum'
conn=mysql.connector.connect(user=os.environ.get('USERNAME'), password='prod', host='localhost', database='axiom', charset='utf8mb4', auth_plugin='mysql_native_password')
cur=conn.cursor()
cur.execute("select caller from hierarchy where user='py' and callee=%s",(old,))
print('hier callee', cur.fetchall())
cur.execute("select caller from hierarchy where user='py' and caller=%s",(old,))
print('hier caller', cur.fetchall())
cur.execute("select caller,callee from `function` where user='py' and (caller=%s or callee=%s)",(old,old))
print('func', cur.fetchall())
cur.execute("select axiom,state from axiom where user='py' and axiom in (%s,%s)",(old,new))
print('axiom', cur.fetchall())
conn.close()
