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
import Def.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part3
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

theorem boundaryGhost_boltzmannJ_eq_common_mul_base_mul_countFactor
    (d n : ℕ) (β H : ℝ) (σ : BoundaryGhostConfig d n) :
    Sharpness.boltzmannJ (Sharpness.withGhost (FK.boxGraph d n)) β
        (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) σ
      =
      Real.exp (β * H *
          ((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ)) *
        boundaryGhostOriginalBase d n β σ *
          boundaryGhostCountFactor d n β H σ := by
  unfold boundaryGhostOriginalBase boundaryGhostCountFactor
    countHardFieldFactor
  unfold Sharpness.boltzmannJ
  rw [boundaryGhost_weightedBondSum_eq_original_add_mismatch]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring


end Exact3D
end StatMech
