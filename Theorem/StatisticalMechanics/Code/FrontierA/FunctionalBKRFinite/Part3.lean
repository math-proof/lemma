/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part3


namespace StatMech.FrontierA

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem cylinderMin_eventIndicator (A : Set (ConfigSpace E)) (K : Set E)
    (omega : ConfigSpace E) :
    cylinderMin (eventIndicator A) K omega =
      eventIndicator {eta | OccursOn A K eta} omega := by
  classical
  by_cases hocc : OccursOn A K omega
  · change cylinderMin (A.indicator fun _ => (1 : ℝ)) K omega =
      {eta | OccursOn A K eta}.indicator (fun _ => (1 : ℝ)) omega
    rw [Set.indicator_of_mem hocc]
    apply Finset.inf'_eq_of_forall
    intro eta heta
    have hmem : eta ∈ A := hocc eta (mem_agreementFiber.mp heta)
    simp [hmem]
  · change cylinderMin (A.indicator fun _ => (1 : ℝ)) K omega =
      {eta | OccursOn A K eta}.indicator (fun _ => (1 : ℝ)) omega
    rw [Set.indicator_of_notMem hocc]
    simp only [OccursOn] at hocc
    push Not at hocc
    obtain ⟨eta, hagree, hnotmem⟩ := hocc
    apply le_antisymm
    · calc
        cylinderMin (eventIndicator A) K omega
            ≤ eventIndicator A eta := Finset.inf'_le _ (mem_agreementFiber.mpr hagree)
        _ = 0 := by simp [eventIndicator, hnotmem]
    · exact cylinderMin_nonneg
        (fun eta => Set.indicator_nonneg (fun _ _ => zero_le_one) eta) K omega


end StatMech.FrontierA
