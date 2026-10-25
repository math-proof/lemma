/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalDegreeTwoRecoverableReconnection.toHallRouting
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoRecoverableReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade where
  direct source := reconnection.target source.1 false
  direct_injective := by
    intro first second heq
    apply Subtype.ext
    exact reconnection.source_recoverable
      first.1 false second.1 false heq
  direct_supported := reconnection.direct_supported
  paired source branch := reconnection.target source.1 branch
  paired_distinct := reconnection.paired_distinct
  paired_supported := reconnection.paired_supported
  paired_output_recovers_occurrence := by
    intro branch first second heq
    have hsource : first.1 = second.1 :=
      reconnection.source_recoverable
        first.1 branch second.1 branch heq
    have hsubtype : first = second := Subtype.ext hsource
    rw [hsubtype]
  paired_injective_with_occurrence := by
    intro branch first second _ heq
    apply Subtype.ext
    exact reconnection.source_recoverable
      first.1 branch second.1 branch heq
  direct_paired_disjoint := by
    intro directSource pairedSource branch heq
    have hsource : directSource.1 = pairedSource.1 :=
      reconnection.source_recoverable
        directSource.1 false pairedSource.1 branch heq
    exact directSource.2 (hsource ▸ pairedSource.2)


def SixVertexHorizontalDegreeTwoHighChargeHallRouting.PairedRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade) : Prop :=
  ∃ branch, routing.paired source branch = target

end
end StatMech.FrontierD
