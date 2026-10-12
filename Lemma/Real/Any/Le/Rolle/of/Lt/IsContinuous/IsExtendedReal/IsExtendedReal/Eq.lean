import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hlt : a < b)
  (hcont : ContinuousOn f (Set.Icc a b))
  (_ : DifferentiableOn ℝ f (Set.Ioo a b))
  (heq : f a = f b) :
-- imply
  ∃ x ∈ Set.Ioo a b, deriv f x * deriv f x ≤ 0 := by
-- proof
  obtain ⟨x, hx, hx0⟩ := exists_deriv_eq_zero hlt hcont heq
  refine ⟨x, hx, ?_⟩
  simp [hx0]


-- created on 2026-10-11
-- updated on 2026-10-12
