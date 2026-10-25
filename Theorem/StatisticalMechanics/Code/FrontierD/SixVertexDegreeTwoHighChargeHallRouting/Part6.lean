/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedMatching_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    Function.Injective routing.pairedMatching :=
  (Classical.choose_spec
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      routing.PairedRelated).mp routing.paired_hall)).1

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedMatching_related
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) (source) :
    routing.PairedRelated source (routing.pairedMatching source) :=
  (Classical.choose_spec
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      routing.PairedRelated).mp routing.paired_hall)).2 source


end
end StatMech.FrontierD
