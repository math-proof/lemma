/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/


import Def.Order.PosetMatrix
import Lemma.Set.PosetMatrix
import Mathlib.Tactic.FinCases


namespace MetaMathlibExt

/-- The empty `0 × 0` matrix is vacuously a poset matrix. -/
def emptyMat : Matrix (Fin 0) (Fin 0) Bool :=
  fun _ _ => false

end MetaMathlibExt
