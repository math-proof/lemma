/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredVertexCrossFineRowProfile
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap


namespace StatMech.FrontierD

noncomputable section

def sixVertexFinSideOfMedialSide : FKMedialSide -> Fin 4
  | .west => 0
  | .east => 1
  | .south => 2
  | .north => 3

def sixVertexTorusDartOfMedialDart
    {T : EvenTorus} (d : FKMedialDart T) : SixVertexTorusDart T :=
  (d.1, sixVertexFinSideOfMedialSide d.2)

end
end StatMech.FrontierD
