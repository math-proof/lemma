/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6core.Part3
import Def.StatisticalMechanics.Code.Walls.rc7core.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


theorem rc7_deficitBridge_iff_reimerCardFormAll :
    rc7_DeficitBridge ↔ ReimerCardFormAll := by
  constructor
  · intro h n A B; exact (rc5_core_reimerCardForm_iff_deficit A B).mpr (h n A B)
  · intro h n A B; exact (rc5_core_reimerCardForm_iff_deficit A B).mp (h n A B)


theorem rc7_reimerCardFormAll_of_deficitBridge (h : rc7_DeficitBridge) : ReimerCardFormAll :=
  rc7_deficitBridge_iff_reimerCardFormAll.mp h


theorem rc7_naiveBoxCompression_refuted :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
      (boxDoubled (Down.compression i 𝒜)
        (UV.compression ({i} : Finset (Fin 2)) ∅ ℬ)).card
      < (boxDoubled 𝒜 ℬ).card :=
  rc_core_downUp_box_refuted


theorem rc7_reimerCardFormAll_iff_residue :
    ReimerCardFormAll ↔ ReimerResidue :=
  rc5_core_reimerCardFormAll_iff_residue

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rc7_reimer_inequality_of_deficitBridge (h : rc7_DeficitBridge) {E : Type*}
    [Fintype E] [DecidableEq E] {p : NNReal} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc6_reimer_inequality_of_injectionAll
    (rc5_core_injectionAll_of_reimerCardFormAll (rc7_reimerCardFormAll_of_deficitBridge h)) hp A B


theorem rc7_deficit_rbi : rc5_deficit rbi_A rbi_B ≤ 0 :=
  rc5_deficit_rbi


theorem rc7_deficit_one (A B : Set (ConfigSpace (Fin 1))) : rc5_deficit A B ≤ 0 :=
  rc5_deficit_one A B


theorem rc7_cardform_all :
    (rc7_DeficitBridge ↔ ReimerCardFormAll)
      ∧ (rc7_DeficitBridge → ReimerCardFormAll)
      ∧ (ReimerCardFormAll ↔ ReimerResidue)
      ∧ (∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
          (boxDoubled (Down.compression i 𝒜)
            (UV.compression ({i} : Finset (Fin 2)) ∅ ℬ)).card
          < (boxDoubled 𝒜 ℬ).card) :=
  ⟨rc7_deficitBridge_iff_reimerCardFormAll,
    rc7_reimerCardFormAll_of_deficitBridge,
    rc7_reimerCardFormAll_iff_residue,
    rc7_naiveBoxCompression_refuted⟩

end StatMech.Walls
