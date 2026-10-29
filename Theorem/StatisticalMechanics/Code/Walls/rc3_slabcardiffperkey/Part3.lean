/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc2_slabcardallisbridge
import Def.StatisticalMechanics.Code.Walls.rc3_slabcardiffperkey.Part2
open Finset
open scoped FinsetFamily NNReal


namespace StatMech.Walls

open StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc3_perKeyAll_iff_slabCardAll : rc3_PerKeyAll ↔ StatMech.poc_SlabCardAll := by
  unfold rc3_PerKeyAll StatMech.poc_SlabCardAll
  refine forall_congr' (fun n => forall_congr' (fun A => forall_congr' (fun B => ?_)))
  exact (rc3_slabCard_iff_perKey A B).symm


theorem rc3_reimerWprobCore_of_perKeyAll (h : rc3_PerKeyAll) : ReimerWprobCore :=
  rc2_reimerWprobCore_of_slabCardAll (rc3_perKeyAll_iff_slabCardAll.mp h)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rc3_reimer_inequality_of_perKeyAll (h : rc3_PerKeyAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : NNReal} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_slabCard (rc3_perKeyAll_iff_slabCardAll.mp h) hp A B


theorem rc3_perKey_rbi (k : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    rc3_PerKey rbi_A rbi_B k :=
  (rc3_slabCard_iff_perKey rbi_A rbi_B).mp poc_slabCard_rbi k


theorem rc3_perKey_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T)
    (k : ConfigSpace α × ConfigSpace α) :
    rc3_PerKey A B k :=
  (rc3_slabCard_iff_perKey A B).mp (poc_slabCard_of_disjoint_support hA hB hST) k


theorem rc3_perKey_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) (k : ConfigSpace α × ConfigSpace α) :
    rc3_PerKey A B k :=
  (rc3_slabCard_iff_perKey A B).mp (poc_slabCard_of_box_empty hbox) k

end StatMech.Walls
