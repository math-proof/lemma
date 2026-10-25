/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamPatternPreservation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamPatternPreservation


namespace StatMech.FrontierD

noncomputable section

def fkRectUnitGapColumn (R : FKRectTorus) : Fin R.width :=
  ⟨1, lt_trans Nat.one_lt_two R.width_gt_two⟩

end
end StatMech.FrontierD
