module
public import Def.Order.PosetMatrix
public import Theorem.Set.PosetMatrix
public import Mathlib.Tactic.FinCases
public import Def.MathlibExtTest.Order.PosetMatrix.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/
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
