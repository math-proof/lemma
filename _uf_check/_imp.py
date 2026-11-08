from util import *
from Lemma import Set, Finset, Bool, Tensor, Nat, Int, Fin
print('Tensor ok', hasattr(Tensor, 'AppendHstackS'), hasattr(Tensor, 'All_InDotSwapMatrix'))
from Lemma import Matrix
print('Matrix has Append', hasattr(Matrix, 'AppendHstackS'))
print('Matrix has All_In', hasattr(Matrix, 'All_InDotSwapMatrix'))
print('Matrix has SetOf', hasattr(Matrix, 'SetOfDotGetSwapMatrix'))
print('Matrix has Dot', hasattr(Matrix, 'Dot'))
print('Append path', Matrix.AppendHstackS.eq.MatProd_SwapMatrix.of.Le)
print('All_In path', Matrix.All_InDotSwapMatrix.of.Eq_SetOf_EqRange)
# sympy Matrix still?
print('Matrix callable?', callable(Matrix), type(Matrix))
try:
  m = Matrix((0,1))
  print('sympy Matrix still works?', m)
except Exception as e:
  print('sympy Matrix broken after import:', type(e), e)
