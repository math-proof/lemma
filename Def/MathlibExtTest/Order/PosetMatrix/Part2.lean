/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/

module

public import Def.Order.PosetMatrix
public import Theorem.Set.PosetMatrix
public import Mathlib.Tactic.FinCases
public import Theorem.MathlibExtTest.Order.PosetMatrix

@[expose] public section

namespace MetaMathlibExt

/-- The `1 × 1` matrix whose single (diagonal) entry is `true`. -/
def oneMat : Matrix (Fin 1) (Fin 1) Bool :=
  fun _ _ => true

end MetaMathlibExt
