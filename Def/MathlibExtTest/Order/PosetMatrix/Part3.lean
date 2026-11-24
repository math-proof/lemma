module
public import Def.Order.PosetMatrix
public import Theorem.Set.PosetMatrix
public import Mathlib.Tactic.FinCases
public import Theorem.MathlibExtTest.Order.PosetMatrix.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/
namespace MetaMathlibExt

/-- The `2 × 2` total-order matrix: entries on and above the diagonal are `true`. -/
def twoMat : Matrix (Fin 2) (Fin 2) Bool :=
  fun i j => decide ((i : ℕ) ≤ (j : ℕ))

end MetaMathlibExt
