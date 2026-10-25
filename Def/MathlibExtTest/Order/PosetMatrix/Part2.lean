/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/


import Def.Order.PosetMatrix
import Lemma.Set.PosetMatrix
import Mathlib.Tactic.FinCases
import Theorem.MathlibExtTest.Order.PosetMatrix


namespace MetaMathlibExt

/-- The `1 × 1` matrix whose single (diagonal) entry is `true`. -/
def oneMat : Matrix (Fin 1) (Fin 1) Bool :=
  fun _ _ => true

end MetaMathlibExt
