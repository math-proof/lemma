/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/


import Def.Order.PosetMatrix
import Lemma.Set.PosetMatrix
import Mathlib.Tactic.FinCases
import Theorem.MathlibExtTest.Order.PosetMatrix.Part3


namespace MetaMathlibExt

/-- A `3 × 3` upper-triangular Boolean matrix with `true` diagonal that fails
transitivity at `(0, 1)`, `(1, 2)`: the `(0, 2)`-entry is `false`. -/
def badMat : Matrix (Fin 3) (Fin 3) Bool :=
  fun i j => decide ((i : ℕ) ≤ (j : ℕ) ∧ ¬((i : ℕ) = 0 ∧ (j : ℕ) = 2))

end MetaMathlibExt
