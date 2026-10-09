import Mathlib.Analysis.Calculus.Deriv.MeanValue
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b x0 x1 : ℝ}
-- given
  (hd : ∀ x ∈ Set.Ioo a b, 0 < deriv f x)
  (hc : ContinuousOn f (Set.Icc a b))
  (hx0 : x0 ∈ Set.Ioo a b)
  (hx1 : x1 ∈ Set.Ioo a b)
  (hlt : x0 < x1) :
-- imply
  f x0 < f x1 := by
-- proof
  obtain ⟨hax0, hx0b⟩ := Set.mem_Ioo.mp hx0
  obtain ⟨hax1, hx1b⟩ := Set.mem_Ioo.mp hx1
  have hconv : Convex ℝ (Set.Icc x0 x1) := convex_Icc x0 x1
  have hc' : ContinuousOn f (Set.Icc x0 x1) :=
    hc.mono (Set.Icc_subset_Icc hax0.le hx1b.le)
  have hd' : ∀ x ∈ interior (Set.Icc x0 x1), 0 < deriv f x := by
    rw [interior_Icc]
    intro x hx
    exact hd x (Set.Ioo_subset_Ioo hax0.le hx1b.le hx)
  have hs : StrictMonoOn f (Set.Icc x0 x1) :=
    strictMonoOn_of_deriv_pos hconv hc' hd'
  exact hs (Set.left_mem_Icc.mpr hlt.le) (Set.right_mem_Icc.mpr hlt.le) hlt


-- created on 2020-04-30
-- updated on 2023-05-14
