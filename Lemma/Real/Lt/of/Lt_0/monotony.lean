import Mathlib
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b x : ℝ}
-- given
  (hcont : ContinuousOn f (Set.Icc a b))
  (hf : ∀ t ∈ Set.Ioo a b, deriv f t < 0)
  (hx : x ∈ Set.Ioc a b) :
-- imply
  f x < f a := by
-- proof
  obtain ⟨hxa, hxb⟩ := Set.mem_Ioc.mp hx
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) hcont _ (Set.left_mem_Icc.mpr (hxa.le.trans hxb))
    (Set.Ioc_subset_Icc_self hx) hxa
  · apply fun t ht ↦ hf t (by simpa using ht)


-- created on 2026-10-07
