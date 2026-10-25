/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part5


namespace StatMech.FrontierA

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] [DecidableEq E] in
theorem mem_dualDisjointOccurrence {A B : Set (ConfigSpace E)}
    {omega eta : ConfigSpace E} :
    (omega, eta) ∈ dualDisjointOccurrence A B ↔
      ∃ K L : Set E, Disjoint K L ∧ OccursOn A K omega ∧ OccursOn B L eta :=
  Iff.rfl

omit [Fintype E] [DecidableEq E] in


@[simp] theorem dualDisjointOccurrence_diagonal (A B : Set (ConfigSpace E))
    (omega : ConfigSpace E) :
    (omega, omega) ∈ dualDisjointOccurrence A B ↔
      omega ∈ disjointOccurrence A B :=
  Iff.rfl


theorem functionalDisjointMaxAt_eventIndicator (A B : Set (ConfigSpace E))
    (omega eta : ConfigSpace E) :
    functionalDisjointMaxAt (eventIndicator A) (eventIndicator B) omega eta =
      (dualDisjointOccurrence A B).indicator (fun _ => (1 : ℝ)) (omega, eta) := by
  classical
  by_cases hdual : (omega, eta) ∈ dualDisjointOccurrence A B
  · rw [Set.indicator_of_mem hdual]
    obtain ⟨K, L, hKL, hAK, hBL⟩ := hdual
    apply le_antisymm
    · apply Finset.sup'_le
      intro pair hpair
      rw [cylinderMin_eventIndicator, cylinderMin_eventIndicator]
      by_cases hA : OccursOn A pair.1 omega <;>
        by_cases hB : OccursOn B pair.2 eta <;> simp [eventIndicator, hA, hB]
    · have hpair : (K, L) ∈ disjointCoordinatePairs E := by
        simpa using hKL
      calc
        (1 : ℝ) = cylinderMin (eventIndicator A) K omega *
            cylinderMin (eventIndicator B) L eta := by
              rw [cylinderMin_eventIndicator, cylinderMin_eventIndicator]
              simp [eventIndicator, hAK, hBL]
        _ ≤ functionalDisjointMaxAt (eventIndicator A) (eventIndicator B) omega eta :=
          by
            unfold functionalDisjointMaxAt
            exact Finset.le_sup'
              (fun pair : Set E × Set E =>
                cylinderMin (eventIndicator A) pair.1 omega *
                  cylinderMin (eventIndicator B) pair.2 eta)
              hpair
  · rw [Set.indicator_of_notMem hdual]
    apply Finset.sup'_eq_of_forall
    intro pair hpair
    rw [cylinderMin_eventIndicator, cylinderMin_eventIndicator]
    have hnot : ¬ (OccursOn A pair.1 omega ∧ OccursOn B pair.2 eta) := by
      intro hocc
      exact hdual ⟨pair.1, pair.2, mem_disjointCoordinatePairs.mp hpair,
        hocc.1, hocc.2⟩
    by_cases hA : OccursOn A pair.1 omega <;>
      by_cases hB : OccursOn B pair.2 eta <;> simp_all [eventIndicator]


theorem functionalDisjointMax_eventIndicator (A B : Set (ConfigSpace E))
    (omega : ConfigSpace E) :
    functionalDisjointMax (eventIndicator A) (eventIndicator B) omega =
      (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) omega := by
  classical
  rw [functionalDisjointMax, functionalDisjointMaxAt_eventIndicator]
  by_cases h : omega ∈ disjointOccurrence A B
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
    exact dualDisjointOccurrence_diagonal A B omega |>.mpr h
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    exact fun hdual => h (dualDisjointOccurrence_diagonal A B omega |>.mp hdual)

end StatMech.FrontierA
