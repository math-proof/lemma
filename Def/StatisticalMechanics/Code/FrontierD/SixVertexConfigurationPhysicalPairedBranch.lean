module
public import Theorem.StatisticalMechanics.Code.FrontierD.FiniteTwoBranchWeightedTransport
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairTotalCMonotone.Part2
public import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch
open Finset Matrix Polynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalPairedBranch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexConfigurationPairTotalCPhysical
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) : Nat :=
  sixVertexTorusCTypeCount pair.1.1 + sixVertexTorusCTypeCount pair.2.1

end
end StatMech.FrontierD
