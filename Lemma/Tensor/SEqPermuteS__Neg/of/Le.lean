import Lemma.Tensor.SEqPermutePermute__Neg.of.Ge
import sympy.Basic


@[main]
private lemma main
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i ≤ d)
  (X : Tensor α s) :
-- imply
  X.permute i (-d) ≃ X.permute i (-i) := by
-- proof
  sorry


-- created on 2025-10-30
