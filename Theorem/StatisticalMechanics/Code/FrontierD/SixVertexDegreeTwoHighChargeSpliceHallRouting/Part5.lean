/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part6


namespace StatMech.FrontierD

noncomputable section

open Finset

namespace SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets

set_option maxHeartbeats 800000 in
theorem paired_source_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    2 ≤ (Finset.univ.filter (targets.PairedRelated source)).card := by
  let certificate : Fin 2 ↪
      {target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade //
        targets.PairedRelated source target} :=
    { toFun := fun branch =>
        ⟨sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
            (targets.branchKey source (finTwoEquiv branch)),
          ⟨finTwoEquiv branch, rfl⟩⟩
      inj' := by
        intro first second heq
        apply finTwoEquiv.injective
        cases hfirst : finTwoEquiv first <;>
          cases hsecond : finTwoEquiv second
        · rfl
        · exfalso
          exact targets.target_distinct source (by
            simpa [hfirst, hsecond] using congrArg Subtype.val heq)
        · exfalso
          exact targets.target_distinct source (by
            simpa [hfirst, hsecond] using (congrArg Subtype.val heq).symm)
        · rfl }
  have hcard := Fintype.card_le_of_embedding certificate
  simpa [Fintype.card_subtype] using hcard

set_option maxHeartbeats 800000 in
theorem paired_inverse_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade) :
    (Finset.univ.filter fun source =>
      targets.PairedRelated source target).card ≤ 2 := by
  have hcard := Fintype.card_le_of_embedding
    (targets.pairedInverseCode target)
  simpa [Fintype.card_subtype] using hcard


theorem paired_hall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
      T middle hmiddle_pos hmiddle_lt grade) :
    ∀ sources : Finset (SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade),
      sources.card ≤
        (Finset.univ.filter fun target => ∃ source,
          source ∈ sources ∧ targets.PairedRelated source target).card := by
  apply finiteRelationHall_of_bidegree targets.PairedRelated 2 (by omega)
  · exact targets.paired_source_degree
  · exact targets.paired_inverse_degree


end SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
end
end StatMech.FrontierD
