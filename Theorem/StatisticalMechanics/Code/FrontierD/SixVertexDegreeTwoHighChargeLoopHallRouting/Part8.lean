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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part9
open Finset


namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 800000 in

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_source_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    2 ≤ (Finset.univ.filter (reconnection.PairedRelated source)).card := by
  let certificate : Fin 2 ↪
      {target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade //
        reconnection.PairedRelated source target} :=
    { toFun := fun branch =>
        ⟨sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
            (reconnection.key source.1 (finTwoEquiv branch)),
          ⟨finTwoEquiv branch, rfl⟩⟩
      inj' := by
        intro first second heq
        apply finTwoEquiv.injective
        cases hfirst : finTwoEquiv first <;>
          cases hsecond : finTwoEquiv second
        · rfl
        · exfalso
          exact reconnection.high_distinct source (by
            simpa [hfirst, hsecond] using congrArg Subtype.val heq)
        · exfalso
          exact reconnection.high_distinct source (by
            simpa [hfirst, hsecond] using (congrArg Subtype.val heq).symm)
        · rfl }
  have hcard := Fintype.card_le_of_embedding certificate
  simpa [Fintype.card_subtype] using hcard

set_option maxHeartbeats 800000 in

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_inverse_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) :
    (Finset.univ.filter fun source =>
      reconnection.PairedRelated source target).card ≤ 2 := by
  have hcard := Fintype.card_le_of_embedding
    (reconnection.pairedInverseCode target)
  simpa [Fintype.card_subtype] using hcard

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_hall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    ∀ sources : Finset (SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade),
      sources.card ≤
        (Finset.univ.filter fun target => ∃ source,
          source ∈ sources ∧ reconnection.PairedRelated source target).card := by
  apply finiteRelationHall_of_bidegree
    reconnection.PairedRelated 2 (by omega)
  · exact reconnection.paired_source_degree
  · exact reconnection.paired_inverse_degree


end
end StatMech.FrontierD
