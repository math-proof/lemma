import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Order.PosetMatrix


namespace MetaMathlibExt

/--
[twoMat_ok](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean)
-/
@[path]
private lemma twoMat_ok :
  IsPosetMatrix 2 twoMat := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · intro j
      fin_cases j
      · decide
      · decide
    · intro j
      fin_cases j
      · decide
      · decide
  · intro i
    fin_cases i
    · decide
    · decide
  · intro i
    fin_cases i
    · intro j
      fin_cases j
      · intro k
        fin_cases k
        · decide
        · decide
      · intro k
        fin_cases k
        · decide
        · decide
    · intro j
      fin_cases j
      · intro k
        fin_cases k
        · decide
        · decide
      · intro k
        fin_cases k
        · decide
        · decide

end MetaMathlibExt


-- created on 2026-10-23
