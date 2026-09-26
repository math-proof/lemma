import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import sympy.Basic
open Set


@[main]
private lemma main
  {φ φ' φ'' : ℝ → ℝ}
  {M : ℝ}
-- given
  (h₀ : ContinuousOn φ (Icc 0 1))
  (h₁ : ∀ t ∈ Ioo 0 1, HasDerivAt φ (φ' t) t)
  (h₂ : ContinuousOn φ' (Icc 0 1))
  (h₃ : ∀ t ∈ Ioo 0 1, HasDerivAt φ' (φ'' t) t)
  (h₄ : ∀ t ∈ Ioo 0 1, φ'' t ≤ M) :
-- imply
  φ 1 ≤ φ 0 + φ' 0 + M / 2 := by
-- proof
  have hI : interior (Icc (0 : ℝ) 1) = Ioo 0 1 := interior_Icc
  have hφ' : ∀ t ∈ Icc (0 : ℝ) 1, φ' t - φ' 0 ≤ M * (t - 0) := fun t ht =>
    (convex_Icc 0 1).image_sub_le_mul_sub_of_deriv_le h₂
      (fun s hs => (h₃ s (hI ▸ hs)).differentiableAt.differentiableWithinAt)
      (fun s hs => (h₃ s (hI ▸ hs)).deriv ▸ h₄ s (hI ▸ hs)) 0 ⟨le_rfl, zero_le_one⟩ t ht ht.1
  have hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t => φ t - φ' 0 * t - M / 2 * t ^ 2) (φ' s - φ' 0 - M * s) s := fun s hs =>
    (((h₁ s hs).sub ((hasDerivAt_id' s).const_mul (φ' 0))).sub ((hasDerivAt_pow 2 s).const_mul (M / 2))).congr_deriv (by simp; ring)
  have hg := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le (f := fun t => φ t - φ' 0 * t - M / 2 * t ^ 2) (C := 0)
    ((h₀.sub (continuousOn_const.mul continuousOn_id)).sub (continuousOn_const.mul (continuousOn_id.pow 2)))
    (fun s hs => (hd s (hI ▸ hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [(hd s (hI ▸ hs)).deriv]
      linarith [hφ' s (Ioo_subset_Icc_self (hI ▸ hs))])
    0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp at hg
  linarith


-- created on 2026-09-26