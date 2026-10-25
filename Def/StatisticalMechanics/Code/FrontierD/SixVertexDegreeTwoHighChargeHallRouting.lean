/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalDegreeTwoHighCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) : Prop :=
  let pair := sixVertexHorizontalActualDeficitConfigurationPair source
  ∃ hdegree : SixVertexLocallyDegreeTwo pair.1.1.1 pair.1.2.1,
    ∃ component :
        (sixVertexDegreeTwoSynchronizedGraph pair.1.1.2.1 pair.1.2.2.1
          hdegree).ConnectedComponent,
      2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge
        pair.1.1.2.1 pair.1.2.2.1 hdegree component

end
end StatMech.FrontierD
