/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_source_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    2 ≤ (Finset.univ.filter (routing.PairedRelated source)).card := by
  let certificate : Fin 2 ↪
      {target : SixVertexHorizontalDegreeTwoHallTarget T middle
          hmiddle_pos hmiddle_lt grade //
        routing.PairedRelated source target} :=
    { toFun := fun branch =>
        ⟨routing.paired source (finTwoEquiv branch),
          ⟨finTwoEquiv branch, rfl⟩⟩
      inj' := by
        intro first second heq
        have hinjective : Function.Injective (routing.paired source) := by
          intro firstBranch secondBranch hbranch
          cases firstBranch <;> cases secondBranch
          · rfl
          · exact False.elim (routing.paired_distinct source hbranch)
          · exact False.elim (routing.paired_distinct source hbranch.symm)
          · rfl
        apply finTwoEquiv.injective
        apply hinjective
        exact congrArg Subtype.val heq }
  have hcard := Fintype.card_le_of_embedding certificate
  simpa [Fintype.card_subtype] using hcard

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_inverse_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade) :
    (Finset.univ.filter fun source =>
      routing.PairedRelated source target).card ≤ 2 := by
  have hcard := Fintype.card_le_of_embedding
    (routing.pairedInverseCode target)
  simpa [SixVertexHorizontalDegreeTwoHighChargeHallRouting.PairedRelated,
    Fintype.card_subtype] using hcard


theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_hall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    ∀ sources : Finset
        (SixVertexHorizontalDegreeTwoHighChargeSources T middle
          hmiddle_pos hmiddle_lt grade),
      sources.card ≤
        (Finset.univ.filter fun target => ∃ source,
          source ∈ sources ∧ routing.PairedRelated source target).card := by
  apply finiteRelationHall_of_bidegree routing.PairedRelated 2 (by omega)
  · exact routing.paired_source_degree
  · exact routing.paired_inverse_degree


end
end StatMech.FrontierD
