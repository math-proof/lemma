/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Def.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part2
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {E : Type*}


lemma evXor_inter_evXnor : evXor ∩ evXnor = ∅ := by
  ext ω
  simp only [evXor, evXnor, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  exact fun h hc => h hc


lemma not_isIncreasing_evXor : ¬ IsIncreasing evXor := by
  intro h
  set ω : ConfigSpace (Fin 2) := fun i => if i = 0 then true else false with hω
  set ω' : ConfigSpace (Fin 2) := fun _ => true with hω'
  have hle : ω ≤ ω' := by intro i; simp only [hω, hω']; exact Bool.le_true _
  have hmem : ω ∈ evXor := by simp only [evXor, Set.mem_setOf_eq, hω]; decide
  have hcontra := h hle hmem
  simp only [evXor, Set.mem_setOf_eq, hω'] at hcontra
  exact hcontra rfl


lemma not_isDecreasing_evXor : ¬ IsDecreasing evXor := by
  intro h
  set ω : ConfigSpace (Fin 2) := fun i => if i = 0 then true else false with hω
  set ω' : ConfigSpace (Fin 2) := fun _ => false with hω'
  have hle : ω' ≤ ω := by intro i; simp only [hω, hω']; exact Bool.false_le _
  have hmem : ω ∈ evXor := by simp only [evXor, Set.mem_setOf_eq, hω]; decide
  have hcontra := h hle hmem
  simp only [evXor, Set.mem_setOf_eq, hω'] at hcontra
  exact hcontra rfl

set_option linter.unusedSectionVars false in


theorem reimer_xor_xnor_inequality {p : NNReal} (hp : p ≤ 1) :
    (bernoulliProductMeasure (E := Fin 2) p hp).real (disjointOccurrence evXor evXnor)
      ≤ (bernoulliProductMeasure (E := Fin 2) p hp).real evXor
        * (bernoulliProductMeasure (E := Fin 2) p hp).real evXnor :=
  reimer_inequality_of_inter_empty hp evXor_inter_evXnor


end StatMech
