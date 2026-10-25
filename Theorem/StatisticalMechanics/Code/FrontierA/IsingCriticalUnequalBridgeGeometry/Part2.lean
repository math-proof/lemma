/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeEndpoint
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part2


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Filter Topology

noncomputable section

theorem oddPrismCriticalLowerHalfSpinAverage_nonneg (n : Nat) :
    0 <= oddPrismCriticalLowerHalfSpinAverage n := by
  unfold oddPrismCriticalLowerHalfSpinAverage
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro q _
    exact oddPrismLowerHalfSurfaceSpinMeanAt_nonneg
      (Ising.betaC 3) isingBetaC_three_pos.le n q.1 q.2
  · positivity


theorem oddPrismCriticalLowerHalfSpinAverage_sq_le (n : Nat) :
    oddPrismCriticalLowerHalfSpinAverage n ^ 2 <=
      oddPrismCriticalLowerHalfSpinSquareAverage n := by
  let f : Fin (2 * n + 1) × Fin (2 * n + 1) -> Real := fun q =>
    oddPrismLowerHalfSurfaceSpinMeanAt (Ising.betaC 3) n q.1 q.2
  have hL : (0 : Real) < ((2 * n + 1 : Nat) : Real) := by positivity
  have hL2 : (0 : Real) < (((2 * n + 1 : Nat) : Real) ^ 2) :=
    sq_pos_of_pos hL
  have hcs : (∑ q, f q) ^ 2 <=
      (((2 * n + 1 : Nat) : Real) ^ 2) * ∑ q, f q ^ 2 := by
    simpa [f, pow_two] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ) (f := f))
  unfold oddPrismCriticalLowerHalfSpinAverage
    oddPrismCriticalLowerHalfSpinSquareAverage
  change ((∑ q, f q) / (((2 * n + 1 : Nat) : Real) ^ 2)) ^ 2 <=
    (∑ q, f q ^ 2) / (((2 * n + 1 : Nat) : Real) ^ 2)
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos hL2)]
  calc
    (∑ q, f q) ^ 2 <=
        (((2 * n + 1 : Nat) : Real) ^ 2) * ∑ q, f q ^ 2 := hcs
    _ = ((∑ q, f q ^ 2) / (((2 * n + 1 : Nat) : Real) ^ 2)) *
        (((2 * n + 1 : Nat) : Real) ^ 2) ^ 2 := by
      field_simp [hL.ne']


theorem oddPrismCriticalLowerHalfSpinAverage_tendsto_zero :
    Tendsto oddPrismCriticalLowerHalfSpinAverage atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n =>
      Real.sqrt (oddPrismCriticalLowerHalfSpinSquareAverage n))
      atTop (nhds 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp
      oddPrismCriticalLowerHalfSpinSquareAverage_tendsto_zero
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall
      oddPrismCriticalLowerHalfSpinAverage_nonneg
  · exact Filter.Eventually.of_forall (fun n =>
      (Real.le_sqrt
        (oddPrismCriticalLowerHalfSpinAverage_nonneg n)
        (oddPrismCriticalLowerHalfSpinSquareAverage_nonneg n)).2
          (oddPrismCriticalLowerHalfSpinAverage_sq_le n))
  · exact hsqrt


end
end StatMech.FrontierA
