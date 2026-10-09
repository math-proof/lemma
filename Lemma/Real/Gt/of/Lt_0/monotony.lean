import Mathlib
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b x : ℝ}
-- given
  (hcont : ContinuousOn f (Set.Icc a b))
  (hf : ∀ t ∈ Set.Ioo a b, deriv f t < 0)
  (hx : x ∈ Set.Ico a b) :
-- imply
  f b < f x := by
-- proof
  obtain ⟨hxa, hxb⟩ := Set.mem_Ico.mp hx
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) hcont _ (Set.Ico_subset_Icc_self hx)
    (Set.right_mem_Icc.mpr (hxa.trans hxb.le)) hxb
  · apply fun t ht ↦ hf t (by simpa using ht)


-- created on 2026-10-09
