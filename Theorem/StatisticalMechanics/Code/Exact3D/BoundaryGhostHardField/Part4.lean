/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Def.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part4
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

theorem boundaryGhostCountFactor_tendsto (d n : ℕ)
    {β : ℝ} (hβ : 0 < β) (σ : BoundaryGhostConfig d n) :
    Tendsto (fun H : ℝ => boundaryGhostCountFactor d n β H σ)
      atTop
      (𝓝 (boundaryGhostAlignedLimitFactor d n σ)) := by
  have hscale : 0 < 2 * β := by linarith
  exact countHardFieldFactor_tendsto
    (boundaryGhostMismatchCount d n) hscale σ


theorem boundaryGhostCountFactorRatio_tendsto (d n : ℕ)
    {β : ℝ} (hβ : 0 < β)
    (base obs : BoundaryGhostConfig d n → ℝ)
    (hden :
      finiteFactorLimitDenominator
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        base (boundaryGhostAlignedLimitFactor d n) ≠ 0) :
    Tendsto
      (fun H : ℝ =>
        finiteFactorRatio
          (Finset.univ : Finset (BoundaryGhostConfig d n))
          base obs (boundaryGhostCountFactor d n β) H)
      atTop
      (𝓝
        (finiteFactorLimitRatio
          (Finset.univ : Finset (BoundaryGhostConfig d n))
          base obs (boundaryGhostAlignedLimitFactor d n))) := by
  exact finiteFactorRatio_tendsto
    (Finset.univ : Finset (BoundaryGhostConfig d n))
    base obs (boundaryGhostAlignedLimitFactor d n)
    (boundaryGhostCountFactor d n β)
    (fun σ _hσ => boundaryGhostCountFactor_tendsto d n hβ σ)
    hden


theorem boundaryGhostExpectationJ_eq_countFactorRatio
    (d n : ℕ) (β H : ℝ) :
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph d n)) β
        (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
        (finiteBoundaryGhostOnePointSource d n)
      =
      finiteFactorRatio
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostOnePointObservable d n)
        (boundaryGhostCountFactor d n β) H := by
  classical
  let C : ℝ :=
    Real.exp (β * H *
      ((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ))
  have hC : C ≠ 0 := Real.exp_ne_zero _
  have hnum :
      (∑ σ : BoundaryGhostConfig d n,
          Ising.spinProd (finiteBoundaryGhostOnePointSource d n) σ *
            Sharpness.boltzmannJ (Sharpness.withGhost (FK.boxGraph d n)) β
              (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
              σ)
        =
      C * finiteFactorNumerator
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostOnePointObservable d n)
        (boundaryGhostCountFactor d n β) H := by
    unfold finiteFactorNumerator
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [boundaryGhost_boltzmannJ_eq_common_mul_base_mul_countFactor]
    simp [C, boundaryGhostOnePointObservable]
    ring
  have hden :
      Sharpness.partitionJ (Sharpness.withGhost (FK.boxGraph d n)) β
          (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
        =
      C * finiteFactorDenominator
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostCountFactor d n β) H := by
    unfold Sharpness.partitionJ finiteFactorDenominator
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [boundaryGhost_boltzmannJ_eq_common_mul_base_mul_countFactor]
    simp [C]
    ring
  unfold Sharpness.expectationJ finiteFactorRatio
  rw [hnum, hden]
  exact mul_div_mul_left _ _ hC


theorem finiteBoundaryGhostCurrentOnePoint_eq_countFactorRatio
    (d n : ℕ) (β H : ℝ) :
    finiteBoundaryGhostCurrentOnePoint d n β H =
      finiteFactorRatio
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostOnePointObservable d n)
        (boundaryGhostCountFactor d n β) H := by
  rw [finiteBoundaryGhostCurrentOnePoint_eq_expectationJ,
    boundaryGhostExpectationJ_eq_countFactorRatio]


end Exact3D
end StatMech
