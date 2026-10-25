/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose.Part4
import Def.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part5
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


lemma r2k_rbi_box_fst {ω : ConfigSpace (Fin 2)} (hω : ω ∈ disjointOccurrence rbi_A rbi_B) :
    ω 0 = false := by
  rw [rbi_box_eq] at hω
  rcases hω with h | h
  · rw [h]; rfl
  · rw [Set.mem_singleton_iff] at h; rw [h]; rfl


theorem r2k_swapInjection_rbi : r2k_SwapInjection rbi_A rbi_B := by
  classical
  refine ⟨r2k_rbi_swap, ?_, ?_⟩
  · 
    rintro ⟨ω, τ⟩ hp
    have hω0 : ω 0 = false := r2k_rbi_box_fst hp
    
    simp only [swapPair_fst, swapPair_snd, rbi_A, rbi_B, Set.mem_setOf_eq, swapGlue_apply,
      r2k_rbi_swap, hω0, Fin.isValue,
      show ((1 : Fin 2) = 0) = False from by decide, if_false]
    
    clear hp hω0
    cases ω 1 <;> cases τ 0 <;> cases τ 1 <;> decide
  · 
    rintro ⟨ω, τ⟩ hp ⟨ω', τ'⟩ hp' heq
    have hω0 : ω 0 = false := r2k_rbi_box_fst hp
    have hω0' : ω' 0 = false := r2k_rbi_box_fst hp'
    
    have e1 := congrArg (fun q => q.1) heq
    have e2 := congrArg (fun q => q.2) heq
    simp only [swapPair_fst, swapPair_snd] at e1 e2
    have e10 := congrFun e1 0; have e11 := congrFun e1 1
    have e20 := congrFun e2 0; have e21 := congrFun e2 1
    simp only [swapGlue_apply, r2k_rbi_swap, hω0, hω0', Fin.isValue,
      show ((1 : Fin 2) = 0) = False by decide, if_false] at e10 e11 e20 e21
    
    have hext : ω 1 = ω' 1 ∧ τ 0 = τ' 0 ∧ τ 1 = τ' 1 →
        (⟨ω, τ⟩ : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) = ⟨ω', τ'⟩ := by
      rintro ⟨h1, h2, h3⟩
      refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;>
        simp_all [Fin.isValue]
    apply hext
    
    clear hp hp' heq e1 e2 hω0 hω0' hext
    revert e10 e11 e20 e21
    cases ω 1 <;> cases ω' 1 <;> cases τ 0 <;> cases τ 1 <;>
      cases τ' 0 <;> cases τ' 1 <;> decide

end StatMech
