/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
import Def.StatisticalMechanics.Code.Walls.bc122carrier.Part4
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

variable {d : ℕ}


theorem bc122_starRel_tip_forces_hub {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j : Fin 3} {w : Site d}
    (h : bc122_starRel ω L R arm (arm y j) w ∨ bc122_starRel ω L R arm w (arm y j)) :
    w = y := by
  obtain ⟨_, hdistinct, hnohub⟩ := hHBA
  obtain ⟨hybox, hytri⟩ := bc122_mem_hubs.mp hy
  
  have key : ∀ z ∈ bc122_hubs ω L R, ∀ k : Fin 3,
      (arm y j = z ∧ w = arm z k) ∨ (w = z ∧ arm y j = arm z k) → w = y := by
    intro z hz k hcase
    obtain ⟨hzbox, hztri⟩ := bc122_mem_hubs.mp hz
    rcases hcase with ⟨heq, _⟩ | ⟨hwz, hleafeq⟩
    · 
      exact absurd heq (hnohub y hybox hytri z hzbox hztri j)
    · 
      obtain ⟨hyz, _⟩ := hdistinct y hybox hytri z hzbox hztri j k hleafeq
      rw [hwz, hyz]
  rcases h with ⟨z, hz, k, hor⟩ | ⟨z, hz, k, hor⟩
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key z hz k (Or.inl ⟨h1, h2⟩)
    · exact key z hz k (Or.inr ⟨h1, h2⟩)
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key z hz k (Or.inr ⟨h1, h2⟩)
    · exact key z hz k (Or.inl ⟨h1, h2⟩)


theorem bc122_starGraph_tip_adj_forces_hub {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j : Fin 3}
    {lv w' : ↑(bc122_carrier ω L R arm)} (hlv : (lv : Site d) = arm y j)
    (hadj : (bc122_starGraph ω L R arm).Adj lv w') : (w' : Site d) = y := by
  rw [bc122_starGraph, SimpleGraph.fromRel_adj] at hadj
  obtain ⟨hne, hrel⟩ := hadj
  rw [hlv] at hrel
  exact bc122_starRel_tip_forces_hub hHBA hy hrel


theorem bc122_tip_isolated_in_cut {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j : Fin 3}
    (hub lv : ↑(bc122_carrier ω L R arm)) (hhub : (hub : Site d) = y)
    (hlv : (lv : Site d) = arm y j) (w' : ↑(bc122_carrier ω L R arm)) :
    ¬ ((bc122_starGraph ω L R arm).deleteIncidenceSet hub).Adj lv w' := by
  intro hadj
  rw [deleteIncidenceSet_adj] at hadj
  obtain ⟨hstar, hlvne, hw'ne⟩ := hadj
  have : (w' : Site d) = y := bc122_starGraph_tip_adj_forces_hub hHBA hy hlv hstar
  exact hw'ne (Subtype.ext (by rw [this, hhub]))


theorem bc122_tips_not_reachable_in_cut {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j k : Fin 3}
    (hub lv₁ lv₂ : ↑(bc122_carrier ω L R arm)) (hhub : (hub : Site d) = y)
    (hlv₁ : (lv₁ : Site d) = arm y j) (hlv₂ : (lv₂ : Site d) = arm y k)
    (hne : lv₁ ≠ lv₂) :
    ¬ ((bc122_starGraph ω L R arm).deleteIncidenceSet hub).Reachable lv₁ lv₂ := by
  intro hreach
  obtain ⟨p⟩ := hreach
  cases p with
  | nil => exact hne rfl
  | @cons _ c _ hadj q =>
    exact bc122_tip_isolated_in_cut hHBA hy hub lv₁ hhub hlv₁ c hadj


theorem bc122_starGraph_hub_adj_tip {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d}
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j : Fin 3}
    (hub lv : ↑(bc122_carrier ω L R arm)) (hhub : (hub : Site d) = y)
    (hlv : (lv : Site d) = arm y j)
    (hne : hub ≠ lv) :
    (bc122_starGraph ω L R arm).Adj hub lv := by
  rw [bc122_starGraph, SimpleGraph.fromRel_adj]
  refine ⟨hne, Or.inl ?_⟩
  rw [hhub, hlv]
  exact ⟨y, hy, j, Or.inl ⟨rfl, rfl⟩⟩


theorem bc122_starGraph_adj_tip_form {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d}
    {a b : ↑(bc122_carrier ω L R arm)} (hab : (bc122_starGraph ω L R arm).Adj a b) :
    (∃ y ∈ bc122_hubs ω L R, ∃ j : Fin 3, (a : Site d) = arm y j ∧ (b : Site d) = y) ∨
    (∃ y ∈ bc122_hubs ω L R, ∃ j : Fin 3, (b : Site d) = arm y j ∧ (a : Site d) = y) := by
  rw [bc122_starGraph, SimpleGraph.fromRel_adj] at hab
  obtain ⟨hne, hrel⟩ := hab
  rcases hrel with ⟨y, hy, j, hor⟩ | ⟨y, hy, j, hor⟩
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨y, hy, j, h2, h1⟩
    · exact Or.inl ⟨y, hy, j, h2, h1⟩
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨y, hy, j, h2, h1⟩
    · exact Or.inr ⟨y, hy, j, h2, h1⟩


theorem bc122_tip_isolated_after_edge_delete {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {y : Site d} (hy : y ∈ bc122_hubs ω L R) {j : Fin 3}
    (hub lv : ↑(bc122_carrier ω L R arm)) (hhub : (hub : Site d) = y)
    (hlv : (lv : Site d) = arm y j) (w' : ↑(bc122_carrier ω L R arm)) :
    ¬ ((bc122_starGraph ω L R arm).deleteEdges {s(hub, lv)}).Adj lv w' := by
  intro hadj
  rw [SimpleGraph.deleteEdges_adj] at hadj
  obtain ⟨hstar, hnotdel⟩ := hadj
  
  have hw'y : (w' : Site d) = y := bc122_starGraph_tip_adj_forces_hub hHBA hy hlv hstar
  have hw'hub : w' = hub := Subtype.ext (by rw [hw'y, hhub])
  apply hnotdel
  rw [hw'hub, Set.mem_singleton_iff, Sym2.eq_swap]


theorem bc122_starGraph_edge_isBridge {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
    {a b : ↑(bc122_carrier ω L R arm)} (hab : (bc122_starGraph ω L R arm).Adj a b) :
    (bc122_starGraph ω L R arm).IsBridge s(a, b) := by
  rw [SimpleGraph.isBridge_iff]
  refine ⟨hab, ?_⟩
  intro hreach
  
  rcases bc122_starGraph_adj_tip_form hab with ⟨y, hy, j, haT, hbH⟩ | ⟨y, hy, j, hbT, haH⟩
  · 
    obtain ⟨p⟩ := hreach
    cases p with
    | nil => exact hab.ne rfl
    | @cons _ c _ hadj q =>
      
      have hadj' : ((bc122_starGraph ω L R arm).deleteEdges {s(b, a)}).Adj a c := by
        rw [Sym2.eq_swap]; exact hadj
      exact bc122_tip_isolated_after_edge_delete hHBA hy b a hbH haT c hadj'
  · 
    obtain ⟨p⟩ := hreach
    
    have hreach' : ((bc122_starGraph ω L R arm).deleteEdges {s(a, b)}).Reachable b a := ⟨p.reverse⟩
    obtain ⟨q⟩ := hreach'
    cases q with
    | nil => exact hab.ne rfl
    | @cons _ c _ hadj r =>
      exact bc122_tip_isolated_after_edge_delete hHBA hy a b haH hbT c hadj


theorem bc122_starGraph_acyclic {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm) :
    (bc122_starGraph ω L R arm).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  exact bc122_starGraph_edge_isBridge hHBA hab


end StatMech.Walls
