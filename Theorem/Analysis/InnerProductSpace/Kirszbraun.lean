/-
Authors: toskua, Avocado, Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open Finset
open scoped InnerProductSpace


-- N1: weighted variance identity
theorem kirszbraun_sum_mul_mul_norm_sub_sq_eq
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (u : ι → G) (z : G)
    (hsum : ∑ i ∈ s, a i = 1) :
    ∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖u i - u j‖ ^ 2
      = 2 * ∑ i ∈ s, a i * ‖u i - z‖ ^ 2 - 2 * ‖∑ i ∈ s, a i • u i - z‖ ^ 2 := by
  set v : ι → G := fun i => u i - z with hv
  have hvv : ∀ i j, u i - u j = v i - v j := fun i j => by
    simp [hv, sub_sub_sub_cancel_right]
  have hsumv : ∑ i ∈ s, a i • v i = (∑ i ∈ s, a i • u i) - z := by
    simp only [hv, smul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_smul]
    simp [hsum]
  have hexpand : ∀ i j : ι, ‖v i - v j‖ ^ 2
      = ‖v i‖ ^ 2 - 2 * ⟪v i, v j⟫_ℝ + ‖v j‖ ^ 2 := fun i j => by
    have h := norm_sub_sq_real (v i) (v j)
    linarith [h]
  calc ∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖u i - u j‖ ^ 2
      = ∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖v i - v j‖ ^ 2 := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hvv]
    _ = ∑ i ∈ s, ∑ j ∈ s, (a i * a j * ‖v i‖ ^ 2 - a i * a j * (2 * ⟪v i, v j⟫_ℝ) + a i * a j * ‖v
        j‖ ^ 2) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hexpand]; ring
    _ = (∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖v i‖ ^ 2)
        - (∑ i ∈ s, ∑ j ∈ s, a i * a j * (2 * ⟪v i, v j⟫_ℝ))
        + (∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖v j‖ ^ 2) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = 2 * ∑ i ∈ s, a i * ‖v i‖ ^ 2 - 2 * ‖∑ i ∈ s, a i • v i‖ ^ 2 := by
        have h1 : ∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖v i‖ ^ 2 = ∑ i ∈ s, a i * ‖v i‖ ^ 2 := by
          apply Finset.sum_congr rfl; intro i hi
          have hmul : (∑ j ∈ s, a i * a j * ‖v i‖ ^ 2) = a i * ‖v i‖ ^ 2 * (∑ j ∈ s, a j) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
          rw [hmul, hsum, mul_one]
        have h2 : ∑ i ∈ s, ∑ j ∈ s, a i * a j * ‖v j‖ ^ 2 = ∑ i ∈ s, a i * ‖v i‖ ^ 2 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro j hj
          have hmul : (∑ i ∈ s, a i * a j * ‖v j‖ ^ 2) = a j * ‖v j‖ ^ 2 * (∑ i ∈ s, a i) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
          rw [hmul, hsum, mul_one]
        have hcross : ∑ i ∈ s, ∑ j ∈ s, a i * a j * (2 * ⟪v i, v j⟫_ℝ)
            = 2 * ‖∑ i ∈ s, a i • v i‖ ^ 2 := by
          have hinner : ∑ i ∈ s, ∑ j ∈ s, a i * a j * ⟪v i, v j⟫_ℝ
              = ⟪∑ i ∈ s, a i • v i, ∑ j ∈ s, a j • v j⟫_ℝ := by
            rw [sum_inner]
            apply Finset.sum_congr rfl; intro i hi
            rw [inner_sum]
            apply Finset.sum_congr rfl; intro j hj
            rw [real_inner_smul_left, real_inner_smul_right]; ring
          have hnorm : ⟪∑ i ∈ s, a i • v i, ∑ j ∈ s, a j • v j⟫_ℝ = ‖∑ i ∈ s, a i • v i‖ ^ 2 := by
            rw [real_inner_self_eq_norm_sq]
          have hscale : ∑ i ∈ s, ∑ j ∈ s, a i * a j * (2 * ⟪v i, v j⟫_ℝ)
              = 2 * (∑ i ∈ s, ∑ j ∈ s, a i * a j * ⟪v i, v j⟫_ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j hj; ring
          rw [hscale, hinner, hnorm]
        rw [h1, h2, hcross]
        ring
    _ = 2 * ∑ i ∈ s, a i * ‖u i - z‖ ^ 2 - 2 * ‖∑ i ∈ s, a i • u i - z‖ ^ 2 := by
        rw [← hsumv]

