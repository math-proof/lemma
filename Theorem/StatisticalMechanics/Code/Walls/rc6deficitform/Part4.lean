/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6deficitform.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part3
import Def.StatisticalMechanics.Code.Walls.rc6deficitform.Part3
open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc6_deficitNonpos_iff_reimerCardFormAll :
    rc6_DeficitNonpos ↔ ReimerCardFormAll := by
  unfold rc6_DeficitNonpos ReimerCardFormAll
  constructor
  · intro h n A B; exact (rc6_reimerCardForm_iff_deficit A B).mpr (h n A B)
  · intro h n A B; exact (rc6_reimerCardForm_iff_deficit A B).mp (h n A B)


open Classical in

theorem rc6_deficit_rbi : rc6_deficit rbi_A rbi_B ≤ 0 :=
  (rc6_reimerCardForm_iff_deficit rbi_A rbi_B).mp rc3_core_reimerCardForm_rbi

open Classical in


theorem rc6_deficit_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    rc6_deficit A B ≤ 0 :=
  (rc6_reimerCardForm_iff_deficit A B).mp
    (rc3_core_reimerCardForm_of_disjoint_support hA hB hST)

open Classical in


theorem rc6_deficit_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : rc6_deficit A B ≤ 0 :=
  (rc6_reimerCardForm_iff_deficit A B).mp (rc3_core_reimerCardForm_of_box_empty hbox)

open Classical in


theorem rc6_deficit_one (A B : Set (ConfigSpace (Fin 1))) : rc6_deficit A B ≤ 0 :=
  (rc6_reimerCardForm_iff_deficit A B).mp (rc3_core_reimerCardForm_one A B)


open Classical in


theorem rc6_deficit_form (A B : Set (ConfigSpace α)) :
    Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α)
      ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => rmr_compl ω ∈ B))
          = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)))
      ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))
          = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)))
      ∧ (StatMech.poc_ReimerCardForm A B ↔ rc6_deficit A B ≤ 0) :=
  ⟨rc6_compl_involutive, rc6_card_compl_mem B, rc6_RHS_eq_inter A B,
    rc6_reimerCardForm_iff_deficit A B⟩

end StatMech.Walls
