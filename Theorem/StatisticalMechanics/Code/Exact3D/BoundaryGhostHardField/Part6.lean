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
import Structure.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostAlignedLimitIdentification_of_pos
    (d n : ℕ) {β : ℝ} (hβ : 0 < β) :
    FiniteBoundaryGhostAlignedLimitIdentification d n β where
  beta_pos := hβ
  limit_eq_wired := boundaryGhostAlignedLimitRatio_eq_wiredOnePoint d n β


theorem finiteBoundaryGhostCountFactorDictionary_of_alignedLimitIdentification
    {d n : ℕ} {β : ℝ}
    (D : FiniteBoundaryGhostAlignedLimitIdentification d n β) :
    FiniteBoundaryGhostCountFactorDictionary d n β
      (boundaryGhostOriginalBase d n β)
      (boundaryGhostOnePointObservable d n) where
  beta_pos := D.beta_pos
  current_eq := finiteBoundaryGhostCurrentOnePoint_eq_countFactorRatio d n β
  denominator_ne_zero := boundaryGhostAlignedLimitDenominator_ne_zero d n β
  limit_eq_wired := D.limit_eq_wired


theorem finiteBoundaryGhostFactorDictionary_of_countFactorDictionary
    {d n : ℕ} {β : ℝ}
    {base obs : BoundaryGhostConfig d n → ℝ}
    (D : FiniteBoundaryGhostCountFactorDictionary d n β base obs) :
    FiniteBoundaryGhostFactorDictionary d n β
      base obs (boundaryGhostAlignedLimitFactor d n)
      (boundaryGhostCountFactor d n β) where
  current_eq := D.current_eq
  factor_tendsto := fun σ _hσ =>
    boundaryGhostCountFactor_tendsto d n D.beta_pos σ
  denominator_ne_zero := D.denominator_ne_zero
  limit_eq_wired := D.limit_eq_wired


theorem finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_factorDictionary
    {d n : ℕ} {β : ℝ}
    {base obs limitFactor : BoundaryGhostConfig d n → ℝ}
    {factor : ℝ → BoundaryGhostConfig d n → ℝ}
    (D :
      FiniteBoundaryGhostFactorDictionary d n β
        base obs limitFactor factor) :
    Tendsto (fun H : ℝ => finiteBoundaryGhostCurrentOnePoint d n β H)
      atTop
      (𝓝
        (IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n))) := by
  have ht :
      Tendsto
        (fun H : ℝ =>
          finiteFactorRatio
            (Finset.univ : Finset (BoundaryGhostConfig d n))
            base obs factor H)
        atTop
        (𝓝
          (finiteFactorLimitRatio
            (Finset.univ : Finset (BoundaryGhostConfig d n))
            base obs limitFactor)) :=
    finiteFactorRatio_tendsto
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      base obs limitFactor factor
      D.factor_tendsto D.denominator_ne_zero
  have hfun :
      (fun H : ℝ => finiteBoundaryGhostCurrentOnePoint d n β H)
        =
      (fun H : ℝ =>
        finiteFactorRatio
          (Finset.univ : Finset (BoundaryGhostConfig d n))
          base obs factor H) := by
    funext H
    exact D.current_eq H
  rw [hfun]
  simpa [D.limit_eq_wired] using ht


theorem finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_countFactorDictionary
    {d n : ℕ} {β : ℝ}
    {base obs : BoundaryGhostConfig d n → ℝ}
    (D : FiniteBoundaryGhostCountFactorDictionary d n β base obs) :
    Tendsto (fun H : ℝ => finiteBoundaryGhostCurrentOnePoint d n β H)
      atTop
      (𝓝
        (IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n))) :=
  finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_factorDictionary
    (D := finiteBoundaryGhostFactorDictionary_of_countFactorDictionary D)


end Exact3D
end StatMech
