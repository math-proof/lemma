/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc103contractdeg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc71spanningtree.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc103_reachable_deleteIncidence_of_walk_avoiding {V : Type*} {G H : SimpleGraph V}
    (hHG : H ≤ G) (u : V) {a b : V} (p : H.Walk a b) (hp : ∀ x ∈ p.support, x ≠ u) :
    (G.deleteIncidenceSet u).Reachable a b := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons a c b hac q ih =>
    have hane : a ≠ u := hp a (by simp)
    have hcne : c ≠ u := hp c (by simp [Walk.support_cons])
    have htail : ∀ x ∈ q.support, x ≠ u := by
      intro x hx; exact hp x (by simp [Walk.support_cons, hx])
    have hedge : (G.deleteIncidenceSet u).Adj a c := by
      rw [deleteIncidenceSet_adj]
      exact ⟨hHG hac, hane, hcne⟩
    exact (hedge.reachable).trans (ih htail)


theorem bc103_firstNeighbour_of_arm {V : Type*} {G F : SimpleGraph V} (hFG : F ≤ G)
    (hFreach : ∀ a b, G.Reachable a b → F.Reachable a b) {u v : V}
    (hadj : G.Adj u v) :
    ∃ w, F.Adj u w ∧ (G.deleteIncidenceSet u).Reachable w v := by
  classical
  have hune : u ≠ v := hadj.ne
  have hFr : F.Reachable u v := hFreach u v hadj.reachable
  obtain ⟨p, hp⟩ := hFr.exists_isPath
  
  cases p with
  | nil => exact absurd rfl hune
  | @cons _ w _ hadjuw q =>
    
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    obtain ⟨hqpath, huq⟩ := hp
    refine ⟨w, hadjuw, ?_⟩
    
    have hqavoid : ∀ x ∈ q.support, x ≠ u := by
      intro x hx hxu; subst hxu; exact huq hx
    exact bc103_reachable_deleteIncidence_of_walk_avoiding hFG u q hqavoid


theorem bc103_deg3_of_noBypass {V : Type*} [Fintype V] {G F : SimpleGraph V} [DecidableRel F.Adj]
    (hFG : F ≤ G) (hFreach : ∀ a b, G.Reachable a b → F.Reachable a b) {u v₁ v₂ v₃ : V}
    (hadj₁ : G.Adj u v₁) (hadj₂ : G.Adj u v₂) (hadj₃ : G.Adj u v₃)
    (hcut₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
    (hcut₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
    (hcut₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) :
    3 ≤ F.degree u := by
  classical
  obtain ⟨w₁, hw₁adj, hw₁r⟩ := bc103_firstNeighbour_of_arm hFG hFreach hadj₁
  obtain ⟨w₂, hw₂adj, hw₂r⟩ := bc103_firstNeighbour_of_arm hFG hFreach hadj₂
  obtain ⟨w₃, hw₃adj, hw₃r⟩ := bc103_firstNeighbour_of_arm hFG hFreach hadj₃
  
  have hw12 : w₁ ≠ w₂ := by
    intro h; apply hcut₁₂
    exact (hw₁r.symm.trans (h ▸ hw₂r))
  have hw13 : w₁ ≠ w₃ := by
    intro h; apply hcut₁₃
    exact (hw₁r.symm.trans (h ▸ hw₃r))
  have hw23 : w₂ ≠ w₃ := by
    intro h; apply hcut₂₃
    exact (hw₂r.symm.trans (h ▸ hw₃r))
  exact bc71_deg3_of_three_neighbours F hw₁adj hw₂adj hw₃adj hw12 hw13 hw23


theorem bc103_deg3_spanForest_of_noBypass {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel (osf_spanForest G).Adj] {u v₁ v₂ v₃ : V}
    (hadj₁ : G.Adj u v₁) (hadj₂ : G.Adj u v₂) (hadj₃ : G.Adj u v₃)
    (hcut₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
    (hcut₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
    (hcut₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) :
    3 ≤ (osf_spanForest G).degree u :=
  bc103_deg3_of_noBypass (osf_spanForest_le G)
    (fun _ _ h => osf_spanForest_reachable_of G h)
    hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃


theorem bc103_arms_distinct_of_deleteVert_cut {V : Type*} {G : SimpleGraph V} {u v₁ v₂ v₃ : V}
    (hcut₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
    (hcut₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
    (hcut₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) :
    v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ :=
  ⟨fun h => hcut₁₂ (h ▸ Reachable.refl _),
   fun h => hcut₁₃ (h ▸ Reachable.refl _),
   fun h => hcut₂₃ (h ▸ Reachable.refl _)⟩


end StatMech.Walls
