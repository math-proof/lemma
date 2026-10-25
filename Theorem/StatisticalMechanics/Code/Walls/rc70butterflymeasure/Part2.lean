/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc69doubledmeasure.Part2
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Instance.StatisticalMechanics.Code.Walls.rc70butterflymeasure
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc70_boxDoubled_disjPreserving (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc70_DisjPreserving n (StatMech.boxDoubled 𝒜 ℬ) := by
  intro U hU i
  rw [StatMech.mem_boxDoubled] at hU
  obtain ⟨S, hS, T, hT, hd, rfl⟩ := hU
  rintro ⟨hl, hr⟩
  rw [StatMech.mem_dbl_inl] at hl
  rw [StatMech.mem_dbl_inr] at hr
  exact (Finset.disjoint_left.mp hd hl) hr

set_option maxRecDepth 4000 in


theorem rc70_doubleCompress_breaks_disjPreserving :
    ¬ rc70_DisjPreserving 2
        (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})) := by
  decide

set_option maxRecDepth 4000 in


theorem rc70_broken_member_exists :
    ∃ U ∈ StatMech.doubleCompress (0 : Fin 2) (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}),
      (Sum.inl (0 : Fin 2)) ∈ U ∧ (Sum.inr (0 : Fin 2)) ∈ U := by
  decide


theorem rc70_doubleCompress_card_preserved :
    (StatMech.doubleCompress (0 : Fin 2) (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})).card
      = (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}).card :=
  StatMech.doubleCompress_card 0 _


theorem rc70_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc60_reimerWprobCore_of_boxUnionBound h


theorem rc70_reimerWprobCore_of_residue (h : rc69_DoubledMeasureResidue) : ReimerWprobCore :=
  rc69_reimerWprobCore_of_residue h

open Classical in
set_option maxRecDepth 4000 in


theorem rc70_status :
    
    (∀ (m : ℕ) (Fam : Finset (Finset (Fin m ⊕ Fin m))),
        rc70_measure m (1/2) Fam = Fam.card * (1/2) ^ (2 * m)) ∧
    (∀ (m : ℕ) (i : Fin m) (Fam : Finset (Finset (Fin m ⊕ Fin m))),
        rc70_measure m (1/2) (StatMech.doubleCompress i Fam) = rc70_measure m (1/2) Fam) ∧
    
    ((rc70_measure 2 (3/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})
        < rc70_measure 2 (3/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})))
      ∧ (rc70_measure 2 (1/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}))
        < rc70_measure 2 (1/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}))) ∧
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))), rc70_DisjPreserving m (StatMech.boxDoubled 𝒜 ℬ)) ∧
    (¬ rc70_DisjPreserving 2
        (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}))) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun _m Fam => rc70_measure_half Fam,
   fun _m i Fam => rc70_measure_half_invariant i Fam,
   rc70_weighted_measure_not_monotone,
   fun _m 𝒜 ℬ => rc70_boxDoubled_disjPreserving 𝒜 ℬ,
   rc70_doubleCompress_breaks_disjPreserving,
   rc70_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
