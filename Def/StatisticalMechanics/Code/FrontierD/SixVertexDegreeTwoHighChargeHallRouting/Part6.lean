/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def
    SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedInverseCode
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (output : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade) :
    {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade // routing.PairedRelated source output} ↪
      Fin 2 where
  toFun source := finTwoEquiv.symm
    (routing.pairedInverseBranch output source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    have hbranch : routing.pairedInverseBranch output first =
        routing.pairedInverseBranch output second := by
      apply finTwoEquiv.symm.injective
      exact heq
    apply routing.paired_branch_injective
      (routing.pairedInverseBranch output first)
    calc
      routing.paired first.1 (routing.pairedInverseBranch output first) =
          output := routing.paired_inverse_spec output first
      _ = routing.paired second.1
          (routing.pairedInverseBranch output second) :=
        (routing.paired_inverse_spec output second).symm
      _ = routing.paired second.1
          (routing.pairedInverseBranch output first) := by rw [hbranch]

end
end StatMech.FrontierD
