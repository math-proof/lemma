/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexDegreeTwoUnitStrandPhysicalRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (target : SixVertexConfigurationPhysicalTarget T middle) : Prop :=
  exists hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1,
    exists seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1,
      exists hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1
        source.2.2.1 hdegree seed).sum = 1,
        target = sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree
          seed hunit


end
end StatMech.FrontierD
