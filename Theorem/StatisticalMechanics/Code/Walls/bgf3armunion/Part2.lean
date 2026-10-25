/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfkforestcount
import Def.StatisticalMechanics.Code.Walls.bgf3armunion.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


theorem bgf3_star_witness :
    Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card := by
  classical
  haveI : DecidableRel (bgf3_G bgf3_starRay bgf3_starLen).Adj := Classical.decRel _
  refine bgf3_count bgf3_starRay bgf3_starLen bau_star_witness.1 ?_ ?_ ?_ ?_ ?_
    (fun _ => (0 : Fin 4)) ?_ (fun _ j => j) ?_ ?_ ?_
  · 
    intro j k hk
    simp only [bgf3_starLen] at hk
    interval_cases k
    fin_cases j <;> (simp only [bgf3_starRay]; decide)
  · 
    intro j; simp [bgf3_starLen]
  · 
    intro j n hn m hm hnm
    simp only [Set.mem_setOf_eq, bgf3_starLen] at hn hm
    simp only [bgf3_starRay] at hnm
    interval_cases n <;> interval_cases m <;> fin_cases j <;> simp_all
  · 
    intro v
    fin_cases v
    · exact ⟨0, 0, by simp [bgf3_starLen], by simp [bgf3_starRay]⟩
    · exact ⟨0, 1, by simp [bgf3_starLen], by simp [bgf3_starRay]⟩
    · exact ⟨1, 1, by simp [bgf3_starLen], by simp [bgf3_starRay]⟩
    · exact ⟨2, 1, by simp [bgf3_starLen], by simp [bgf3_starRay]⟩
  · 
    intro j; simp only [bgf3_starLen, bgf3_starRay]; fin_cases j <;> decide
  · 
    intro a b _; exact Subsingleton.elim a b
  · 
    intro i j; simp [bgf3_starRay]
  · 
    intro i j j' hjj'; simp only [bgf3_starRay]; fin_cases j <;> fin_cases j' <;> simp_all
  · 
    intro α; exact ⟨0, by simp [bgf3_starRay]⟩


theorem bgf3_status :
    
    (∀ {V : Type} {Arm : Type} (ray : Arm → ℕ → V) (len : Arm → ℕ) {T : SimpleGraph V},
      T.IsTree → (∀ α, ∀ k < len α, T.Adj (ray α k) (ray α (k + 1))) →
      (bgf3_G ray len).IsAcyclic) ∧
    
    (∀ {V : Type} [Fintype V] {Arm : Type} (ray : Arm → ℕ → V) (len : Arm → ℕ)
        [DecidableRel (bgf3_G ray len).Adj],
      (∀ α, 1 ≤ len α) → (∀ α, Set.InjOn (ray α) {n | n ≤ len α}) →
      ∀ {B : Finset V}, (∀ α, ray α (len α) ∈ B) →
      ∀ {ι : Type} (f : ι → V) (arm3 : ι → Fin 3 → Arm),
      (∀ i j, ray (arm3 i j) 0 = f i) →
      (∀ i (j j' : Fin 3), j ≠ j' → ray (arm3 i j) 1 ≠ ray (arm3 i j') 1) →
      (∀ α, ∃ i, ray α 0 = f i) →
      ∀ {v : V}, (bgf3_G ray len).degree v = 1 → v ∈ B) ∧
    
    (Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V Arm ray len T hT hadjT; exact bgf3_acyclic ray len hT hadjT
  · intro V _ Arm ray len _ hlen hinj B htip ι f arm3 h1 h2 h3 v hv
    exact bgf3_leaves_on_boundary ray len hlen hinj htip f arm3 h1 h2 h3 hv
  · exact bgf3_star_witness

end StatMech.Walls
