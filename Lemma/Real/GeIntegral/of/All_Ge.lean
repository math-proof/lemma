import sympy.integrals.integrals
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : f ∈ ℒ¹ a b)
  (hgi : g ∈ ℒ¹ a b)
  (h : ∀ x ∈ Set.Ioo a b, f x ≥ g x) :
-- imply
  ∫ x : ℝ in a..b, f x ≥ ∫ x : ℝ in a..b, g x :=
-- proof
  intervalIntegral.integral_mono_on_of_le_Ioo hab.le hgi hfi h


-- created on 2026-09-26
