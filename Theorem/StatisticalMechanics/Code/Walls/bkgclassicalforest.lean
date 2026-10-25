/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bgfacyclicstep
import Theorem.StatisticalMechanics.Code.Walls.bararmray
import Theorem.StatisticalMechanics.Code.Walls.bc69count.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkwburtonkeane
import Def.StatisticalMechanics.Code.Walls.bkgclassicalforest
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


@[simp] theorem bkg_deleteVertex_adj {V : Type*} (Amb : SimpleGraph V) (t a b : V) :
    (bkg_deleteVertex Amb t).Adj a b ↔ Amb.Adj a b ∧ a ≠ t ∧ b ≠ t := Iff.rfl


theorem bkg_deleteVertex_adj_of_le {V : Type*} {Amb G : SimpleGraph V} (hle : G ≤ Amb)
    {t a b : V} (hab : G.Adj a b) (ha : a ≠ t) (hb : b ≠ t) :
    (bkg_deleteVertex Amb t).Adj a b :=
  ⟨hle hab, ha, hb⟩


theorem bkg_walkReach_free {V : Type*} {Amb G : SimpleGraph V} (hle : G ≤ Amb) (t : V) :
    ∀ a b (w : G.Walk a b), t ∉ w.support → (bkg_deleteVertex Amb t).Reachable a b :=
  bgf_walkReach G (fun t => bkg_deleteVertex Amb t) t
    (fun a b hab hta htb => (bkg_deleteVertex_adj_of_le hle hab (Ne.symm hta) (Ne.symm htb)).reachable)


theorem bkg_acyclic_of_singleVertexCut {V : Type*} (Amb G : SimpleGraph V) (hle : G ≤ Amb)
    (H1 : ∀ t a b, G.Adj t a → G.Adj t b → a ≠ b →
      ¬ (bkg_deleteVertex Amb t).Reachable a b) :
    G.IsAcyclic :=
  bgf_acyclic_of_reachSep G (fun t => bkg_deleteVertex Amb t) H1
    (fun t a b w hnotin => bkg_walkReach_free hle t a b w hnotin)


theorem bkg_reachable_eq_of_edgeless {V : Type*} {H : SimpleGraph V} (he : ∀ u v, ¬ H.Adj u v)
    {a b : V} (h : H.Reachable a b) : a = b := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (he _ _)


theorem bkg_step_witness : bc70_star4.IsAcyclic := by
  classical
  refine bkg_acyclic_of_singleVertexCut bc70_star4 bc70_star4 le_rfl ?_
  intro t a b hta htb hab
  
  by_cases ht0 : t = 0
  · subst ht0
    intro hreach
    
    have hedgeless : ∀ u v, ¬ (bkg_deleteVertex bc70_star4 0).Adj u v := by
      intro u v ⟨hadj, hu, hv⟩
      have : u = 0 ∨ v = 0 := by
        revert hadj; simp only [bc70_star4, SimpleGraph.fromEdgeSet_adj]
        intro ⟨hmem, _⟩; fin_cases u <;> fin_cases v <;> revert hmem <;> decide
      rcases this with h | h
      · exact hu h
      · exact hv h
    exact hab (bkg_reachable_eq_of_edgeless hedgeless hreach)
  · 
    exfalso
    have hnb : ∀ z, bc70_star4.Adj t z → z = 0 := by
      intro z hz
      revert hz; simp only [bc70_star4, SimpleGraph.fromEdgeSet_adj]
      intro ⟨hmem, _⟩; fin_cases t <;> first | (exact absurd rfl ht0) | (fin_cases z <;> revert hmem <;> decide)
    exact hab ((hnb a hta).trans (hnb b htb).symm)


theorem bkg_trif_three_arms (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R) (y : Site d)
    (arm : Fin 3 → Site d)
    (harmbox : ∀ i, arm i ∈ box d R)
    (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L y) ω) (arm i)).Infinite)
    (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L y).Reachable (arm i) (arm j)) :
    ∃ tip : Fin 3 → Site d,
      (∀ i, (bc67_contractedLattice ω L y).Reachable (arm i) (tip i)) ∧
      (∀ i, tip i ∈ vertexBoundary d R) ∧
      (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L y).Reachable (tip i) (tip j)) := by
  classical
  have htip : ∀ i, ∃ t, (bc67_contractedLattice ω L y).Reachable (arm i) t ∧
      t ∈ vertexBoundary d R := by
    intro i
    obtain ⟨r, hr0, hinj, hadjr, hreachr⟩ :=
      bar_armRay_of_infiniteComponent ω L y (arm i) (harminf i)
    have hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)) := fun k =>
      ((bc67_contractedLattice_le ω L y) (hadjr k)).1
    have h0box : r 0 ∈ box d R := by rw [hr0]; exact harmbox i
    obtain ⟨k, hk⟩ := bar_ray_crosses_boundary r hinj hlat R hR h0box
    exact ⟨r k, hreachr k, hk⟩
  choose tip htipreach htipbdry using htip
  refine ⟨tip, htipreach, htipbdry, ?_⟩
  intro i j hij
  exact bar_armSep_of_rays ω L y (htipreach i) (htipreach j) (harmsep i j hij)


end StatMech.Walls
