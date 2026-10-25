/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Mathlib.Algebra.Order.Chebyshev


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

theorem norm_sub_sq_le_pathLength_mul_sum_dist
    (F : Complex → Complex) (gamma : Nat → Complex)
    (steps : Nat) (C : Real)
    (hstep : ∀ k < steps,
      ‖F (gamma k) - F (gamma (k + 1))‖ ^ 2 ≤
        C * dist (gamma k) (gamma (k + 1))) :
    ‖F (gamma 0) - F (gamma steps)‖ ^ 2 ≤
      (steps : Real) * C *
        ∑ k ∈ Finset.range steps, dist (gamma k) (gamma (k + 1)) := by
  let a : Nat → Real := fun k ↦ dist (F (gamma k)) (F (gamma (k + 1)))
  let d : Nat → Real := fun k ↦ dist (gamma k) (gamma (k + 1))
  have hpath : dist (F (gamma 0)) (F (gamma steps)) ≤
      ∑ k ∈ Finset.range steps, a k :=
    dist_le_range_sum_dist (fun k ↦ F (gamma k)) steps
  have hpathSq : dist (F (gamma 0)) (F (gamma steps)) ^ 2 ≤
      (∑ k ∈ Finset.range steps, a k) ^ 2 := by
    nlinarith [show 0 ≤ dist (F (gamma 0)) (F (gamma steps)) from dist_nonneg,
      Finset.sum_nonneg (s := Finset.range steps) (fun k _ ↦
        (show 0 ≤ dist (F (gamma k)) (F (gamma (k + 1))) from dist_nonneg))]
  have hcauchy : (∑ k ∈ Finset.range steps, a k) ^ 2 ≤
      (steps : Real) * ∑ k ∈ Finset.range steps, a k ^ 2 := by
    simpa [a] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.range steps)
        (f := fun k ↦ dist (F (gamma k)) (F (gamma (k + 1)))))
  have hsum : (∑ k ∈ Finset.range steps, a k ^ 2) ≤
      C * ∑ k ∈ Finset.range steps, d k := by
    calc
      (∑ k ∈ Finset.range steps, a k ^ 2) ≤
          ∑ k ∈ Finset.range steps, C * d k := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_range.mp hk
        simpa [a, d, dist_eq_norm] using hstep k hk'
      _ = C * ∑ k ∈ Finset.range steps, d k := by
        rw [Finset.mul_sum]
  calc
    ‖F (gamma 0) - F (gamma steps)‖ ^ 2 =
        dist (F (gamma 0)) (F (gamma steps)) ^ 2 := by rw [dist_eq_norm]
    _ ≤ (∑ k ∈ Finset.range steps, a k) ^ 2 := hpathSq
    _ ≤ (steps : Real) * ∑ k ∈ Finset.range steps, a k ^ 2 := hcauchy
    _ ≤ (steps : Real) * (C * ∑ k ∈ Finset.range steps, d k) := by
      gcongr
    _ = (steps : Real) * C *
        ∑ k ∈ Finset.range steps, dist (gamma k) (gamma (k + 1)) := by
      simp only [d]
      ring


theorem norm_sub_sq_le_pathLength_sq_mul_mesh
    (F : Complex → Complex) (gamma : Nat → Complex)
    (steps : Nat) (C mesh : Real) (hC : 0 ≤ C)
    (hstepDist : ∀ k < steps,
      dist (gamma k) (gamma (k + 1)) ≤ mesh)
    (hstepHolder : ∀ k < steps,
      ‖F (gamma k) - F (gamma (k + 1))‖ ^ 2 ≤
        C * dist (gamma k) (gamma (k + 1))) :
    ‖F (gamma 0) - F (gamma steps)‖ ^ 2 ≤
      C * (steps : Real) ^ 2 * mesh := by
  have hpath := norm_sub_sq_le_pathLength_mul_sum_dist
    F gamma steps C hstepHolder
  have hsum : (∑ k ∈ Finset.range steps,
      dist (gamma k) (gamma (k + 1))) ≤ (steps : Real) * mesh := by
    calc
      _ ≤ ∑ _k ∈ Finset.range steps, mesh := by
        apply Finset.sum_le_sum
        intro k hk
        exact hstepDist k (Finset.mem_range.mp hk)
      _ = (steps : Real) * mesh := by simp
  calc
    ‖F (gamma 0) - F (gamma steps)‖ ^ 2 ≤
        (steps : Real) * C *
          ∑ k ∈ Finset.range steps, dist (gamma k) (gamma (k + 1)) := hpath
    _ ≤ (steps : Real) * C * ((steps : Real) * mesh) := by
      gcongr
    _ = C * (steps : Real) ^ 2 * mesh := by ring


end
end StatMech.Universality
