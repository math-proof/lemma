/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc115severance.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc34ray.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc117_cut_forceOpen_boxIncident (T : Finset (Site d)) (W : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d)))
    (hW : ∀ e ∈ W, ∃ t ∈ T, t ∈ e) :
    removeSites T (forceOpenFinset W ω) = removeSites T ω := by
  classical
  funext e
  unfold removeSites forceOpenFinset
  by_cases h : ∃ t ∈ T, t ∈ e
  · simp [h]
  · 
    have hnotW : e ∉ W := fun he => h (hW e he)
    simp [h, hnotW]


theorem bc117_cut_connected_boxIncident {T : Finset (Site d)} {W : Finset (Sym2 (Site d))}
    {ω : ConfigSpace (Sym2 (Site d))} (hW : ∀ e ∈ W, ∃ t ∈ T, t ∈ e) {a b : Site d} :
    Connected d (removeSites T (forceOpenFinset W ω)) a b ↔
      Connected d (removeSites T ω) a b := by
  rw [bc117_cut_forceOpen_boxIncident T W ω hW]


theorem bc117_cut_cluster_boxIncident {T : Finset (Site d)} {W : Finset (Sym2 (Site d))}
    {ω : ConfigSpace (Sym2 (Site d))} (hW : ∀ e ∈ W, ∃ t ∈ T, t ∈ e) (a : Site d) :
    cluster d (removeSites T (forceOpenFinset W ω)) a =
      cluster d (removeSites T ω) a := by
  rw [bc117_cut_forceOpen_boxIncident T W ω hW]


theorem bc117_cut_step_of_notMem {T : Finset (Site d)} {ω : ConfigSpace (Sym2 (Site d))}
    {a c : Site d} (hadj : (openSubgraph d ω).Adj a c) (ha : a ∉ T) (hc : c ∉ T) :
    Connected d (removeSites T ω) a c := by
  refine IsOpenEdge.connected ⟨hadj.1, ?_⟩
  rw [show removeSites T ω s(a, c) = ω s(a, c) from ?_]
  · exact hadj.2
  · unfold removeSites
    rw [if_neg]
    rintro ⟨t, ht, htmem⟩
    rw [Sym2.mem_iff] at htmem
    rcases htmem with rfl | rfl
    · exact ha ht
    · exact hc ht


theorem bc117_ray_cut_reach {T : Finset (Site d)} {ω : ConfigSpace (Sym2 (Site d))}
    {r : ℕ → Site d} (hadj : ∀ k, (openSubgraph d ω).Adj (r k) (r (k + 1)))
    (havoid : ∀ k, r k ∉ T) (k : ℕ) :
    Connected d (removeSites T ω) (r 0) (r k) := by
  induction k with
  | zero => exact connected_refl _ (r 0)
  | succ i ih =>
    exact ih.trans (bc117_cut_step_of_notMem (hadj i) (havoid i) (havoid (i + 1)))


theorem bc117_ray_cut_cluster_infinite {T : Finset (Site d)} {ω : ConfigSpace (Sym2 (Site d))}
    {r : ℕ → Site d} (hinj : Function.Injective r)
    (hadj : ∀ k, (openSubgraph d ω).Adj (r k) (r (k + 1)))
    (havoid : ∀ k, r k ∉ T) :
    (cluster d (removeSites T ω) (r 0)).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := r) hinj
  intro k
  rw [mem_cluster]
  exact bc117_ray_cut_reach hadj havoid k


theorem bc117_boxAvoiding_external_infinite (ω : ConfigSpace (Sym2 (Site d))) {v : Site d}
    (hinf : (cluster d ω v).Infinite) (T : Finset (Site d)) :
    ∃ b : Site d, Connected d ω v b ∧ b ∉ T ∧
      (cluster d (removeSites T ω) b).Infinite := by
  obtain ⟨b, hconn, r, hr0, hinj, hadj, havoid⟩ :=
    ray34_Tavoiding_ray_of_infinite_cluster ω hinf T
  refine ⟨b, hconn, ?_, ?_⟩
  · have := havoid 0; rwa [hr0] at this
  · have hinf' := bc117_ray_cut_cluster_infinite hinj hadj havoid
    rwa [hr0] at hinf'


end StatMech.Walls
