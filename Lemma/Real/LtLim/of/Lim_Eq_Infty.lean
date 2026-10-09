import Mathlib
import sympy.Basic
open Filter



@[path]
private lemma main
  {f : ℝ → ℝ}
  {x : ℝ}
-- given
  (h : Filter.Tendsto (fun ε ↦ (f (x + ε) - f x) / ε) (nhdsWithin 0 {0}ᶜ) Filter.atTop) :
-- imply
  ∀ᶠ ε in nhdsWithin 0 (Set.Iio 0), f (x + ε) < f x := by
-- proof
  rw [tendsto_atTop] at h
  have h1 := h 1
  have h2 : ∀ᶠ ε in nhdsWithin 0 (Set.Iio (0 : ℝ)), 1 ≤ (f (x + ε) - f x) / ε :=
    h1.filter_mono (nhdsWithin_mono 0 fun ε hε ↦ ne_of_lt hε)
  filter_upwards [h2, self_mem_nhdsWithin] with ε hε hε_neg
  have hε_lt : ε < 0 := hε_neg
  have h4 : 0 < (f (x + ε) - f x) / ε := by linarith
  have h5 : f (x + ε) - f x < 0 := by
    apply div_pos_iff.mp at h4
    cases h4 with
    | inl h_left => linarith
    | inr h_right => linarith
  linarith


-- created on 2026-10-07
