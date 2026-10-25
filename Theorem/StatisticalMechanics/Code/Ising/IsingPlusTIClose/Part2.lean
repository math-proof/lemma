/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusErgodicClose
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIClose
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

variable {d : ℕ}


theorem iti_prod_coordCM_eq_indicator (T : Finset (Site d)) (ω : ConfigSpace (Site d)) :
    (∏ x ∈ T, pstc_coordCM x ω)
      = (fmu_multiOpen (E := Site d) T).indicator (fun _ => (1:ℝ)) ω := by
  simp only [pstc_coordCM_apply]
  by_cases h : ω ∈ fmu_multiOpen (E := Site d) T
  · rw [Set.indicator_of_mem h]; exact Finset.prod_eq_one fun x hx => by rw [if_pos (h x hx)]
  · rw [Set.indicator_of_notMem h]
    simp only [fmu_multiOpen, Set.mem_setOf_eq, not_forall] at h
    obtain ⟨x, hx, hxx⟩ := h
    exact Finset.prod_eq_zero hx (by rw [if_neg (by simpa using hxx)])

@[simp] theorem iti_monomialCM_apply (T : Finset (Site d)) (ω : ConfigSpace (Site d)) :
    iti_monomialCM T ω = (fmu_multiOpen (E := Site d) T).indicator (fun _ => (1:ℝ)) ω := by
  rw [iti_monomialCM, ContinuousMap.prod_apply]; exact iti_prod_coordCM_eq_indicator T ω


theorem iti_monomialCM_empty : iti_monomialCM (∅ : Finset (Site d)) = 1 := by
  rw [iti_monomialCM, Finset.prod_empty]


theorem iti_monomialCM_singleton (x : Site d) :
    iti_monomialCM ({x} : Finset (Site d)) = pstc_coordCM x := by
  rw [iti_monomialCM, Finset.prod_singleton]


theorem iti_monomialCM_mul (T₁ T₂ : Finset (Site d)) :
    iti_monomialCM T₁ * iti_monomialCM T₂ = iti_monomialCM (T₁ ∪ T₂) := by
  apply ContinuousMap.ext; intro ω
  simp only [ContinuousMap.mul_apply, iti_monomialCM_apply]
  have hinter : fmu_multiOpen (E := Site d) (T₁ ∪ T₂)
      = fmu_multiOpen (E := Site d) T₁ ∩ fmu_multiOpen (E := Site d) T₂ := by
    ext ω'; simp only [fmu_multiOpen, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_union]
    constructor
    · intro hh; exact ⟨fun e he => hh e (Or.inl he), fun e he => hh e (Or.inr he)⟩
    · rintro ⟨h1, h2⟩ e (he | he)
      · exact h1 e he
      · exact h2 e he
  rw [hinter]
  have := Set.inter_indicator_mul (s := fmu_multiOpen (E := Site d) T₁)
    (t := fmu_multiOpen (E := Site d) T₂) (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) ω
  simp only [mul_one] at this
  rw [this]


theorem iti_closure_isMonomial {hh : C(ConfigSpace (Site d), ℝ)}
    (hmem : hh ∈ Submonoid.closure (Set.range (pstc_coordCM (d := d)))) :
    ∃ T : Finset (Site d), hh = iti_monomialCM T := by
  induction hmem using Submonoid.closure_induction with
  | mem x hx => obtain ⟨e, rfl⟩ := hx; exact ⟨{e}, (iti_monomialCM_singleton e).symm⟩
  | one => exact ⟨∅, (iti_monomialCM_empty).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨T₁, rfl⟩ := hx; obtain ⟨T₂, rfl⟩ := hy
    exact ⟨T₁ ∪ T₂, iti_monomialCM_mul T₁ T₂⟩


end Ising
end StatMech
