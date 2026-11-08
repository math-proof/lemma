import traceback
try:
  from util import *
  import Lemma.Matrix.Any_Eq_Dot_MatProd_SwapMatrix as m
  print('module loaded', m)
  # mimic run.py prove if possible
  if hasattr(m, 'prove'):
    print('has prove')
except Exception:
  traceback.print_exc()
