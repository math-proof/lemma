/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.brpreproute.Part2
import Theorem.StatisticalMechanics.Code.Walls.bararmray
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem ben_ray34_gap {V : Type*} [DecidableEq V] {G : SimpleGraph V} [LocallyFinite G] {v : V}
    (hinf : (ray34_AvoidCluster G ∅ v).Infinite) (T : Finset V) :
    ∃ b, ray34_AvoidReach G ∅ v b ∧ (ray34_AvoidCluster G (↑T) b).Infinite := by
  obtain ⟨b, hbmem, hbinf⟩ := ray34_infinite_avoidCluster_of_finset hinf T
  exact ⟨b, hbmem, hbinf⟩


theorem ben_box_adj_avoids (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (t a b : Site d)
    (h : (bc67_contractedLattice ω L t).Adj a b) :
    a ∉ bc61_boxAround d L t ∧ b ∉ bc61_boxAround d L t := by
  rw [bc67_contractedLattice_adj, openSubgraph_adj] at h
  obtain ⟨_, hopen⟩ := h
  unfold removeSites at hopen
  constructor
  · intro ha
    rw [if_pos ⟨a, ha, Sym2.mem_mk_left a b⟩] at hopen; exact absurd hopen (by decide)
  · intro hb
    rw [if_pos ⟨b, hb, Sym2.mem_mk_right a b⟩] at hopen; exact absurd hopen (by decide)


theorem ben_escape_of_notEnclosed (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (tipj x : Site d)
    (hxinf : (cluster d (removeSites (bc61_boxAround d L tipj) ω) x).Infinite) :
    ∃ r : ℕ → Site d, r 0 = x ∧ Function.Injective r ∧
      (∀ k, (bc67_contractedLattice ω L tipj).Adj (r k) (r (k + 1))) ∧
      (∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1))) ∧
      (∀ k, r k ∉ bc61_boxAround d L tipj) := by
  obtain ⟨r, hr0, hinj, hadj, _⟩ := bar_armRay_of_infiniteComponent ω L tipj x hxinf
  refine ⟨r, hr0, hinj, hadj, ?_, ?_⟩
  · intro k; exact ((bc67_contractedLattice_le ω L tipj) (hadj k)).1
  · intro k; exact (ben_box_adj_avoids ω L tipj (r k) (r (k + 1)) (hadj k)).1


theorem ben_ray_reach_in_compl (Bset : Set (Site d)) (r : ℕ → Site d)
    (hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)))
    (havoid : ∀ k, r k ∉ Bset) (k : ℕ) :
    ((hypercubicLattice d).induce Bsetᶜ).Reachable ⟨r 0, havoid 0⟩ ⟨r k, havoid k⟩ := by
  induction k with
  | zero => exact Reachable.refl _
  | succ n ih =>
    have hadj : ((hypercubicLattice d).induce Bsetᶜ).Adj ⟨r n, havoid n⟩ ⟨r (n + 1), havoid (n + 1)⟩ := by
      simp only [SimpleGraph.induce_adj]
      exact hlat n
    exact ih.trans hadj.reachable


theorem ben_ray_reaches_exterior (Bset : Set (Site d)) (R : ℕ) (hBR : Bset ⊆ box d R)
    (r : ℕ → Site d) (hinj : Function.Injective r)
    (hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)))
    (havoid : ∀ k, r k ∉ Bset) :
    ∃ k, r k ∈ exterior d R ∧
      ((hypercubicLattice d).induce Bsetᶜ).Reachable ⟨r 0, havoid 0⟩ ⟨r k, havoid k⟩ := by
  obtain ⟨k, hk⟩ := bar_ray_exits_box r hinj R
  refine ⟨k, ?_, ben_ray_reach_in_compl Bset r hlat havoid k⟩
  rw [exterior_eq_compl_box]; exact hk


theorem ben_escapes_same_fullComponent (F : Finset (Site d)) (hd : 2 ≤ d)
    (r s : ℕ → Site d) (hrinj : Function.Injective r) (hsinj : Function.Injective s)
    (hrlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)))
    (hslat : ∀ k, (hypercubicLattice d).Adj (s k) (s (k + 1)))
    (hravoid : ∀ k, r k ∉ (↑F : Set (Site d)))
    (hsavoid : ∀ k, s k ∉ (↑F : Set (Site d))) :
    ((hypercubicLattice d).induce (↑F : Set (Site d))ᶜ).Reachable
      ⟨r 0, hravoid 0⟩ ⟨s 0, hsavoid 0⟩ := by
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box (↑F : Set (Site d)) F.finite_toSet
  have hsub : exterior d R ⊆ (↑F : Set (Site d))ᶜ :=
    Lattice.exterior_subset_compl (↑F : Set (Site d)) R hR
  obtain ⟨kr, hkr_ext, hkr_reach⟩ := ben_ray_reaches_exterior (↑F) R hR r hrinj hrlat hravoid
  obtain ⟨ks, hks_ext, hks_reach⟩ := ben_ray_reaches_exterior (↑F) R hR s hsinj hslat hsavoid
  
  have hext : ((hypercubicLattice d).induce (↑F : Set (Site d))ᶜ).Reachable
      ⟨r kr, hravoid kr⟩ ⟨s ks, hsavoid ks⟩ := by
    have h := exterior_reachable_compl (↑F : Set (Site d)) R hd hsub (r kr) (s ks) hkr_ext hks_ext
    exact h
  exact (hkr_reach.trans hext).trans hks_reach.symm


end StatMech.Walls
