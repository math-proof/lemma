/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_topkey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Def.StatisticalMechanics.Code.Walls.rmr_topkey
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech StatMech.ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem topKey_slabCard_eq_reimerCardForm (A B : Set (ConfigSpace α)) :
    (#(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey)) ↔ ReimerCardForm A B := by
  rw [topKey_slabBox_eq_box, topKey_slabImg_eq_complImage]; rfl


theorem reimerCardForm_of_slabCard {A B : Set (ConfigSpace α)}
    (h : poc_SlabCard A B) : ReimerCardForm A B :=
  (topKey_slabCard_eq_reimerCardForm A B).mp (h poc_topKey)


theorem reimerCardForm_of_perOrbitCard {A B : Set (ConfigSpace α)}
    (h : PerOrbitCard A B) : ReimerCardForm A B :=
  reimerCardForm_of_slabCard ((poc_perOrbitCard_iff_slabCard A B).mp h)


theorem reimerCardForm_rbi : ReimerCardForm rbi_A rbi_B :=
  reimerCardForm_of_slabCard poc_slabCard_rbi


theorem reimerCardForm_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    ReimerCardForm A B :=
  reimerCardForm_of_slabCard (poc_slabCard_of_disjoint_support hA hB hST)


theorem reimerCardForm_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : ReimerCardForm A B :=
  reimerCardForm_of_slabCard (poc_slabCard_of_box_empty hbox)

end StatMech.Walls
