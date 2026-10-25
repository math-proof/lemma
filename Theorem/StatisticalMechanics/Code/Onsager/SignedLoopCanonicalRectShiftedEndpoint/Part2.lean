/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectEndpoint
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Def.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part2
open MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Sharpness StatMech.FrontierB

noncomputable section

@[simp] theorem ons_originNeighborRectDualPath_source_pullback (n : Nat) :
    ((ons_box2EquivRect (n + 1)).symm
      (ons_originNeighborRectDualPath n).source).1 = (![0, 0] : Site 2) := by
  simp [ons_originNeighborRectDualPath, ons_originPositiveBoxVertex]

@[simp] theorem ons_originNeighborRectDualPath_target_pullback (n : Nat) :
    ((ons_box2EquivRect (n + 1)).symm
      (ons_originNeighborRectDualPath n).target).1 = (![1, 0] : Site 2) := by
  simp [ons_originNeighborRectDualPath, ons_neighborPositiveBoxVertex]


end
end StatMech.Onsager
