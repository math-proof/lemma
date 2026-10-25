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
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part5
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

structure FiniteBoundaryGhostFactorDictionary (d n : ℕ) (β : ℝ)
    (base obs limitFactor : BoundaryGhostConfig d n → ℝ)
    (factor : ℝ → BoundaryGhostConfig d n → ℝ) : Prop where
  current_eq :
    ∀ H : ℝ,
      finiteBoundaryGhostCurrentOnePoint d n β H =
        finiteFactorRatio
          (Finset.univ : Finset (BoundaryGhostConfig d n))
          base obs factor H
  factor_tendsto :
    ∀ σ, σ ∈ (Finset.univ : Finset (BoundaryGhostConfig d n)) →
      Tendsto (fun H : ℝ => factor H σ) atTop (𝓝 (limitFactor σ))
  denominator_ne_zero :
    finiteFactorLimitDenominator
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      base limitFactor ≠ 0
  limit_eq_wired :
    finiteFactorLimitRatio
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      base obs limitFactor =
        IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n)


structure FiniteBoundaryGhostCountFactorDictionary (d n : ℕ) (β : ℝ)
    (base obs : BoundaryGhostConfig d n → ℝ) : Prop where
  beta_pos : 0 < β
  current_eq :
    ∀ H : ℝ,
      finiteBoundaryGhostCurrentOnePoint d n β H =
        finiteFactorRatio
          (Finset.univ : Finset (BoundaryGhostConfig d n))
          base obs (boundaryGhostCountFactor d n β) H
  denominator_ne_zero :
    finiteFactorLimitDenominator
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      base (boundaryGhostAlignedLimitFactor d n) ≠ 0
  limit_eq_wired :
    finiteFactorLimitRatio
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      base obs (boundaryGhostAlignedLimitFactor d n) =
        IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n)


structure FiniteBoundaryGhostAlignedLimitIdentification
    (d n : ℕ) (β : ℝ) : Prop where
  beta_pos : 0 < β
  limit_eq_wired :
    finiteFactorLimitRatio
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      (boundaryGhostOriginalBase d n β)
      (boundaryGhostOnePointObservable d n)
      (boundaryGhostAlignedLimitFactor d n) =
        IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n)


end Exact3D
end StatMech
