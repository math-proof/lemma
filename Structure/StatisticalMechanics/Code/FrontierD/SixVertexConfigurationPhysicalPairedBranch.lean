/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalPairedBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteTwoBranchWeightedTransport
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairTotalCMonotone.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

structure SixVertexConfigurationPhysicalPairedBranchEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) where
  branch : Bool ->
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt ↪
      SixVertexConfigurationPhysicalTarget T middle
  distinct : forall source, branch false source ≠ branch true source
  aggregateTotalC : forall source,
    2 * sixVertexConfigurationPairTotalCPhysical source <=
      sixVertexConfigurationPairTotalCPhysical (branch false source) +
        sixVertexConfigurationPairTotalCPhysical (branch true source)


end
end StatMech.FrontierD
