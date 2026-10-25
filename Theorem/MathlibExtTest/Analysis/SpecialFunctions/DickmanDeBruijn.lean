/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/DickmanDeBruijn.lean -/


import Def.Analysis.SpecialFunctions.DickmanDeBruijn
import Lemma.Real.DickmanDeBruijn
import Mathlib.Tactic.NormNum
open Set


example : Real.IsDickmanDeBruijn = fun ρ : ℝ → ℝ =>
    (∀ u, u < 0 → ρ u = 0) ∧
      MapsTo ρ (Ici (0 : ℝ)) (Icc (0 : ℝ) 1) ∧
      ContinuousOn ρ (Ici (0 : ℝ)) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, ρ u = 1) ∧
      ∀ u, 1 < u → DifferentiableAt ℝ ρ u ∧ u * deriv ρ u + ρ (u - 1) = 0 := by
  rfl

example : ¬ Real.IsDickmanDeBruijn (fun _ : ℝ => 0) := by
  intro h
  have h0 := h.eq_one_of_nonneg_of_le_one (u := 0) (by norm_num) (by norm_num)
  norm_num at h0

example : ¬ Real.IsDickmanDeBruijn (fun _ : ℝ => 1) := by
  intro h
  have hneg := h.eq_zero_of_neg (u := -1) (by norm_num)
  norm_num at hneg

example {ρ : ℝ → ℝ} (h : Real.IsDickmanDeBruijn ρ) {u : ℝ}
    (hu : 0 ≤ u) : ρ u ∈ Icc (0 : ℝ) 1 :=
  h.mem_Icc_of_nonneg hu

example {ρ : ℝ → ℝ} (h : Real.IsDickmanDeBruijn ρ) : ρ 0 = 1 :=
  h.eq_one_of_nonneg_of_le_one (by norm_num) (by norm_num)

example {ρ : ℝ → ℝ} (h : Real.IsDickmanDeBruijn ρ) : ρ 1 = 1 :=
  h.eq_one_of_nonneg_of_le_one (by norm_num) (by norm_num)

example {ρ : ℝ → ℝ} (h : Real.IsDickmanDeBruijn ρ) {u : ℝ}
    (hu : 1 < u) : DifferentiableAt ℝ ρ u :=
  h.differentiableAt_of_one_lt hu

example {ρ : ℝ → ℝ} (h : Real.IsDickmanDeBruijn ρ) {u : ℝ}
    (hu : 1 < u) : u * deriv ρ u + ρ (u - 1) = 0 :=
  h.delay_eq hu

