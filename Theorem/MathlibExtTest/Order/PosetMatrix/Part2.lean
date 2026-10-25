/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/


import Def.Order.PosetMatrix
import Lemma.Set.PosetMatrix
import Mathlib.Tactic.FinCases
import Def.MathlibExtTest.Order.PosetMatrix.Part2


namespace MetaMathlibExt

example : IsPosetMatrix 1 oneMat := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    intro j
    fin_cases j
    decide
  · intro i
    fin_cases i
    decide
  · intro i
    fin_cases i
    intro j
    fin_cases j
    intro k
    fin_cases k
    decide

end MetaMathlibExt
