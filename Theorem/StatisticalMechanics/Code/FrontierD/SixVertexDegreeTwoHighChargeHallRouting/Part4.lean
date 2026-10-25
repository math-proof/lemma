/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_inverse_spec
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (output : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade)
    (source : {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade // routing.PairedRelated source output}) :
    routing.paired source.1 (routing.pairedInverseBranch output source) =
      output :=
  Classical.choose_spec source.2


end
end StatMech.FrontierD
