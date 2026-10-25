/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ConsecutivePolynomial.lean -/


import Def.NumberTheory.ConsecutivePolynomial
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum


namespace MetaMathlibExt

example {k : ℕ} {L : Fin k → Polynomial ℤ} (hL : IsConsecutivePolynomialFamily k L)
    (i : Fin k) (hi : i.val + 1 < k) : L ⟨i.val + 1, hi⟩ - L i = 1 :=
  hL i hi

example : IsConsecutivePolynomialFamily 0 (fun i ↦ Fin.elim0 i) := by
  intro i
  exact Fin.elim0 i

example : IsConsecutivePolynomialFamily 2 (fun i ↦ Polynomial.C (i.val : ℤ)) := by
  intro i hi
  fin_cases i
  · norm_num
  · norm_num at hi

#print axioms MetaMathlibExt.IsConsecutivePolynomialFamily

end MetaMathlibExt
