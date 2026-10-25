/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/


import Def.Order.PosetMatrix
import Lemma.Set.PosetMatrix
import Mathlib.Tactic.FinCases
import Def.MathlibExtTest.Order.PosetMatrix


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
