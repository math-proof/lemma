import Mathlib
import sympy.Basic
open Filter



@[main]
private lemma main
  {f : ℝ → ℝ}
  {x : ℝ}
-- given
  (h : Filter.Tendsto (fun ε ↦ (f (x + ε) - f x) / ε) (nhdsWithin 0 {0}ᶜ) Filter.atTop) :
-- imply
  ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), f (x + ε) > f x := by
-- proof
  rw [tendsto_atTop] at h
  have h1 := h 1
  have h2 : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), 1 ≤ (f (x + ε) - f x) / ε :=
    h1.filter_mono (nhdsWithin_mono 0 fun ε hε ↦ ne_of_gt hε)
  filter_upwards [h2, self_mem_nhdsWithin] with ε hε hε_pos
  have hε_gt : 0 < ε := hε_pos
  have h4 : 0 < (f (x + ε) - f x) / ε := by linarith
  have h5 : 0 < f (x + ε) - f x := by
    apply (div_pos_iff_of_pos_right hε_gt).mp h4
  linarith


-- created on 2026-10-07
