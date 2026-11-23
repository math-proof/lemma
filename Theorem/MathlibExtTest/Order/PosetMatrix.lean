/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/
module

public import Def.Order.PosetMatrix
public import Theorem.Set.PosetMatrix
public import Mathlib.Tactic.FinCases
public import Def.MathlibExtTest.Order.PosetMatrix

public section

namespace MetaMathlibExt

example : IsPosetMatrix 0 emptyMat := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

end MetaMathlibExt
