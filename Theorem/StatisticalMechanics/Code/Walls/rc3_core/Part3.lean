/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc3_slabcardiffperkey.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc3_slabimgeqinter.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc3_doubledboxcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc3_hallforswapinjection
import Theorem.StatisticalMechanics.Code.Walls.rc3_minimalwitnessencoded
import Theorem.StatisticalMechanics.Code.Walls.rc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
import Def.StatisticalMechanics.Code.Walls.rc3_core.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc3_core_residue_of_subcubeReduction
    (hred : ReimerSubcubeReduction) (hcard : ReimerCardFormAll) : ReimerResidue :=
  rc3_core_residue_iff_perKeyAll.mpr (hred hcard)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rc3_core_reimer_inequality_of_subcubeReduction
    (hred : ReimerSubcubeReduction) (hcard : ReimerCardFormAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : NNReal} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc3_core_reimer_inequality_of_residue
    (rc3_core_residue_of_subcubeReduction hred hcard) hp A B


theorem rc3_core_reimerCardFormAll_of_residue (h : ReimerResidue) : ReimerCardFormAll :=
  rc3_core_reimerCardFormAll_of_slabCardAll h


theorem rc3_core_reimerCardForm_rbi : poc_ReimerCardForm rbi_A rbi_B :=
  poc_reimerCardForm_of_slabCard rbi_A rbi_B poc_slabCard_rbi


theorem rc3_core_reimerCardForm_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_ReimerCardForm A B :=
  poc_reimerCardForm_of_slabCard A B (poc_slabCard_of_disjoint_support hA hB hST)


theorem rc3_core_reimerCardForm_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : poc_ReimerCardForm A B :=
  poc_reimerCardForm_of_slabCard A B (poc_slabCard_of_box_empty hbox)


theorem rc3_core_reimerCardForm_one (A B : Set (ConfigSpace (Fin 1))) : poc_ReimerCardForm A B :=
  poc_reimerCardForm_of_slabCard A B (rc_core_bridge_one A B)


set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rc3_core_count_box_bridge :
    (ReimerResidue ↔ rc_core_CountBoxBridge)
      ∧ (ReimerResidue ↔ rc3_PerKeyAll)
      ∧ (ReimerResidue ↔ SlabInjectionAll)
      ∧ (ReimerResidue → ReimerWprobCore)
      ∧ (ReimerResidue → ReimerCardFormAll)
      ∧ (ReimerSubcubeReduction → ReimerCardFormAll → ReimerResidue) :=
  ⟨rc3_core_residue_iff_bridge, rc3_core_residue_iff_perKeyAll,
    rc3_core_residue_iff_slabInjectionAll, rc3_core_reimerWprobCore_of_residue,
    rc3_core_reimerCardFormAll_of_residue, rc3_core_residue_of_subcubeReduction⟩

end StatMech.Walls
