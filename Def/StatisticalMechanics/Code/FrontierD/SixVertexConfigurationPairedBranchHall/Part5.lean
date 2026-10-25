/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairedBranchHall.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexConfigurationPairedBranchConstructions
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    Prop :=
  forall grade, Nonempty
    (SixVertexConfigurationPairedBranchGeometricConstruction T middle
      hmiddle_pos hmiddle_lt grade)

noncomputable def
    sixVertexConfigurationPairedBranchConstructionOfIsEmpty
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (hempty : IsEmpty (SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade)) :
    SixVertexConfigurationPairedBranchGeometricConstruction T middle
      hmiddle_pos hmiddle_lt grade where
  target source := isEmptyElim source
  distinct source := isEmptyElim source
  recoverable _branch first := isEmptyElim first


end
end StatMech.FrontierD
