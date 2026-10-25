/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalCycleCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopThermodynamicLimit.Part3
import Def.StatisticalMechanics.Code.Onsager.SignedLoopCriticalCycleCover
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.FrontierA

noncomputable section

theorem summable_ons_rectDualPathCriticalCycleCoverTerm {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) :
    Summable (ons_rectDualPathCriticalCycleCoverTerm embedding path) :=
  (hasSum_fintype
    (ons_rectDualPathCriticalCycleCoverTerm embedding path)).summable


theorem tsum_ons_rectDualPathCriticalCycleCoverTerm {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) :
    ∑' sigma, ons_rectDualPathCriticalCycleCoverTerm embedding path sigma =
      (ons_sourceX (ons_rectDualGraph M N) {path.source, path.target}
        ons_signedLoopCriticalWeight : Complex) ^ 2 := by
  rw [tsum_fintype]
  unfold ons_rectDualPathCriticalCycleCoverTerm
  rw [← Finset.mul_sum]
  rw [← Matrix.det_apply']
  exact (coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet embedding path
    ons_signedLoopCriticalWeight_pos.ne').symm


end
end StatMech.Onsager
