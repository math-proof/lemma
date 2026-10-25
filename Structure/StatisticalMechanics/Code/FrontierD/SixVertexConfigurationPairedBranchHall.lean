/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairedBranchHall
open Finset


namespace StatMech.FrontierD

noncomputable section

structure SixVertexConfigurationPairedBranchGeometricConstruction
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  target :
    SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade ->
      Bool ->
        SixVertexConfigurationPairBigradeFiber T middle middle grade
  distinct : forall source, target source false ≠ target source true
  recoverable : forall branch first second,
    target first branch = target second branch -> first = second


structure SixVertexConfigurationPairedBranchEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  branch : Bool ->
    SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade ↪
      SixVertexConfigurationPairBigradeFiber T middle middle grade
  distinct : forall source, branch false source ≠ branch true source

end
end StatMech.FrontierD
