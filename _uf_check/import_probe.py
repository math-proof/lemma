import time
print('1 mysql.connector', flush=True)
t=time.time(); import mysql.connector; print('  ok', time.time()-t, flush=True)
print('2 std', flush=True)
t=time.time(); import std; print('  ok', time.time()-t, flush=True)
print('3 pandas', flush=True)
t=time.time()
try:
    import pandas; print('  ok', time.time()-t, flush=True)
except Exception as e:
    print('  skip', e, flush=True)
print('4 tqdm', flush=True)
t=time.time(); from tqdm import tqdm; print('  ok', time.time()-t, flush=True)
print('5 full MySQL', flush=True)
t=time.time(); from sympy import MySQL; print('  ok', time.time()-t, flush=True)
print('DONE', flush=True)
