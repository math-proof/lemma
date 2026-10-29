/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc5_reflectinvolution.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc5_reindextransfer
import Theorem.StatisticalMechanics.Code.Walls.rc5_doubledboxcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc5_dpairsmodular
import Theorem.StatisticalMechanics.Code.Walls.rc5_itercompcard
import Theorem.StatisticalMechanics.Code.Walls.rc5_nonvacuity
import Theorem.StatisticalMechanics.Code.Walls.rc2_core.Part3
import Def.StatisticalMechanics.Code.Walls.rc5_core.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


theorem rc5_core_reimerCardFormAll_of_injectionAll (h : rc5_BoxReflectInjectionAll) :
    ReimerCardFormAll :=
  fun n A B => rc5_core_reimerCardForm_of_injection (h n A B)


theorem rc5_core_injectionAll_of_reimerCardFormAll (h : ReimerCardFormAll) :
    rc5_BoxReflectInjectionAll :=
  fun n A B => rc5_core_injection_of_reimerCardForm (h n A B)


theorem rc5_core_injectionAll_iff_reimerCardFormAll :
    rc5_BoxReflectInjectionAll ↔ ReimerCardFormAll :=
  ⟨rc5_core_reimerCardFormAll_of_injectionAll, rc5_core_injectionAll_of_reimerCardFormAll⟩


theorem rc5_core_reimerCardFormAll_iff_residue : ReimerCardFormAll ↔ ReimerResidue :=
  rc4_residue_iff_reimerCardFormAll.symm


theorem rc5_core_injectionAll_of_residue (h : ReimerResidue) : rc5_BoxReflectInjectionAll :=
  rc5_core_injectionAll_of_reimerCardFormAll (rc3_core_reimerCardFormAll_of_residue h)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rc5_core_reimer_inequality_of_injectionAll (h : rc5_BoxReflectInjectionAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : NNReal} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc4_reimer_inequality_of_reimerCardFormAll
    (rc5_core_reimerCardFormAll_of_injectionAll h) hp A B


section Nonvacuity

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc5_core_injection_rbi : rc5_BoxReflectInjection rbi_A rbi_B :=
  rc5_core_injection_of_reimerCardForm rc5_reimerCardForm_rbi


theorem rc5_core_injection_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    rc5_BoxReflectInjection A B :=
  rc5_core_injection_of_reimerCardForm (rc5_reimerCardForm_of_disjoint_support hA hB hST)


theorem rc5_core_injection_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : rc5_BoxReflectInjection A B :=
  rc5_core_injection_of_reimerCardForm (rc5_reimerCardForm_of_box_empty hbox)


theorem rc5_core_injection_one (A B : Set (ConfigSpace (Fin 1))) : rc5_BoxReflectInjection A B :=
  rc5_core_injection_of_reimerCardForm (rc5_reimerCardForm_one A B)

end Nonvacuity


theorem rc5_core_cardform_all :
    (rc5_DeficitNonpos ↔ ReimerCardFormAll)
      ∧ (ReimerCardFormAll ↔ ReimerResidue)
      ∧ (rc5_BoxReflectInjectionAll ↔ ReimerCardFormAll)
      ∧ (rc5_BoxReflectInjectionAll → ReimerResidue)
      ∧ (ReimerResidue → rc5_BoxReflectInjectionAll) :=
  ⟨rc5_core_deficitNonpos_iff_reimerCardFormAll,
    rc5_core_reimerCardFormAll_iff_residue,
    rc5_core_injectionAll_iff_reimerCardFormAll,
    fun h => rc5_core_reimerCardFormAll_iff_residue.mp
      (rc5_core_reimerCardFormAll_of_injectionAll h),
    rc5_core_injectionAll_of_residue⟩

end StatMech.Walls
