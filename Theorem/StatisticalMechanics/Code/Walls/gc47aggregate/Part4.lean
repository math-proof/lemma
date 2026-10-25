/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc46redistribute.Part2
import Def.StatisticalMechanics.Code.Walls.gc47aggregate.Part4
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

theorem gc47_defectOverflow_card : #gc47_defectOverflow = 6 := by decide


theorem gc47_defectOverflow_subset :
    gc47_defectOverflow ⊆ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3 := by
  rw [gc47_LHSpairs, gc46_defect_Lset, gc47_defectOverflow]
  intro p hp; revert p; decide


theorem gc47_defect_univFibre_card :
    #(({(univ : Finset (Fin 5))} : Finset (Finset (Fin 5))).sigma
        (fun M => gc45_evenSub gc46_defectEnds M)) = 4 := by decide


theorem gc47_defect_no_subset_pairInjection :
    ¬ ∃ Φ : (Σ _ : Finset (Fin 5), Finset (Fin 5)) → (Σ _ : Finset (Fin 5), Finset (Fin 5)),
        (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3,
            Φ p ∈ gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3)
          ∧ Set.InjOn Φ (gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3)
          ∧ (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3, p.1 ⊆ (Φ p).1) := by
  rintro ⟨Φ, hmap, hinj, hsub⟩
  
  have hUniv : ∀ p ∈ gc47_defectOverflow,
      Φ p ∈ ({(univ : Finset (Fin 5))} : Finset (Finset (Fin 5))).sigma
        (fun M => gc45_evenSub gc46_defectEnds M) := by
    intro p hp
    have hpL := gc47_defectOverflow_subset hp
    have hΦR := hmap p hpL
    have hΦsub := hsub p hpL
    
    rw [gc47_RHSpairs, Finset.mem_sigma] at hΦR
    obtain ⟨hΦR1, hΦR2⟩ := hΦR
    
    have hp1 : p.1 = ({0, 1, 3, 4} : Finset (Fin 5)) ∨ p.1 = ({0, 2, 3, 4} : Finset (Fin 5))
        ∨ p.1 = ({1, 2, 3, 4} : Finset (Fin 5)) := by
      rw [gc47_defectOverflow, Finset.mem_sigma] at hp
      have := hp.1
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at this
      exact this
    have hΦ1univ : (Φ p).1 = (univ : Finset (Fin 5)) := by
      
      have hRexp : (Φ p).1 ∈ ({({0, 3, 4} : Finset (Fin 5)), {1, 3, 4}, {2, 3, 4}, univ} :
          Finset (Finset (Fin 5))) := by
        rw [← gc46_defect_Rset]; exact hΦR1
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hRexp
      
      rcases hp1 with h | h | h <;> rw [h] at hΦsub <;>
        rcases hRexp with hR | hR | hR | hR <;> rw [hR] at hΦsub ⊢ <;>
          first
            | rfl
            | (exfalso; revert hΦsub; decide)
    rw [Finset.mem_sigma, Finset.mem_singleton, hΦ1univ]
    exact ⟨rfl, by rw [hΦ1univ] at hΦR2; exact hΦR2⟩
  
  have hle := Finset.card_le_card_of_injOn Φ hUniv
    (Set.InjOn.mono (by exact_mod_cast gc47_defectOverflow_subset) hinj)
  rw [gc47_defectOverflow_card, gc47_defect_univFibre_card] at hle
  omega


theorem gc47_defect_pairLevel_splits :
    gc47_PairInjection gc46_defectEnds (0 : Fin 4) 1 2 3
      ∧ ¬ ∃ Φ : (Σ _ : Finset (Fin 5), Finset (Fin 5)) → (Σ _ : Finset (Fin 5), Finset (Fin 5)),
          (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3,
              Φ p ∈ gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3)
            ∧ Set.InjOn Φ (gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3)
            ∧ (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3, p.1 ⊆ (Φ p).1) :=
  ⟨gc47_defect_pairInjection, gc47_defect_no_subset_pairInjection⟩

end StatMech.Walls
