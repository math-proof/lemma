/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/


import Def.Order.PosetMatrix
import Lemma.Set.PosetMatrix
import Mathlib.Tactic.FinCases
import Theorem.MathlibExtTest.Order.PosetMatrix.Part2


namespace MetaMathlibExt

/-- The `2 × 2` total-order matrix: entries on and above the diagonal are `true`. -/
def twoMat : Matrix (Fin 2) (Fin 2) Bool :=
  fun i j => decide ((i : ℕ) ≤ (j : ℕ))

end MetaMathlibExt
