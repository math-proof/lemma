/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/

module

public import Def.Order.PosetMatrix
public import Theorem.Set.PosetMatrix
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace MetaMathlibExt

/-- The empty `0 × 0` matrix is vacuously a poset matrix. -/
def emptyMat : Matrix (Fin 0) (Fin 0) Bool :=
  fun _ _ => false

end MetaMathlibExt
