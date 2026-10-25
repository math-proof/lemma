/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalDegreeTwoLoopHighCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) : Prop :=
  let pair := source.1.1
  ∃ hdegree : SixVertexLocallyDegreeTwo pair.1.1 pair.2.1,
    ∃ component :
        (sixVertexDegreeTwoSynchronizedGraph pair.1.2.1 pair.2.2.1
          hdegree).ConnectedComponent,
      2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge
        pair.1.2.1 pair.2.2.1 hdegree component

end
end StatMech.FrontierD
