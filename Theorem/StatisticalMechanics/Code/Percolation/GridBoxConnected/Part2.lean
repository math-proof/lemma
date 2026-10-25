/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Def.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
open Set
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


@[simp] lemma mixSite_zero (x y : Site d) : mixSite x y 0 = x := by
  funext i; simp [mixSite]

@[simp] lemma mixSite_full (x y : Site d) : mixSite x y d = y := by
  funext i; simp [mixSite, i.isLt]


lemma mixSite_mem_box {n : ℕ} {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n)
    (k : ℕ) : mixSite x y k ∈ box d n := by
  intro i
  simp only [mixSite]
  by_cases h : (i : ℕ) < k
  · rw [if_pos h]; exact hy i
  · rw [if_neg h]; exact hx i


lemma mixSite_succ {x y : Site d} {k : ℕ} (hk : k < d) :
    mixSite x y (k + 1) = Function.update (mixSite x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) := by
  funext i
  by_cases hik : i = ⟨k, hk⟩
  · subst hik; simp [mixSite, Function.update_self]
  · rw [Function.update_of_ne hik]
    simp only [mixSite]
    have hne : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
    by_cases h : (i : ℕ) < k
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]


lemma connected_mixSite {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    ∀ k ≤ d, Connected d (forceOpenFinset (boxEdges d n) ω) x (mixSite x y k) := by
  intro k
  induction k with
  | zero => intro _; rw [mixSite_zero]
  | succ m ih =>
    intro hsucc
    have hm : m < d := by omega
    have hmle : m ≤ d := by omega
    
    have h1 := ih hmle
    have hstep : Connected d (forceOpenFinset (boxEdges d n) ω)
        (mixSite x y m) (mixSite x y (m + 1)) := by
      rw [mixSite_succ hm]
      exact connected_update ω (mixSite_mem_box hx hy m) ⟨m, hm⟩ (hy ⟨m, hm⟩)
    exact h1.trans hstep


theorem box_allOpen_connected {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    Connected d (forceOpenFinset (boxEdges d n) ω) x y := by
  have h := connected_mixSite ω hx hy d le_rfl
  rwa [mixSite_full] at h


theorem box_allOpen_reachable {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    (openSubgraph d (forceOpenFinset (boxEdges d n) ω)).Reachable x y :=
  box_allOpen_connected ω hx hy


theorem box_allOpen_oneCluster {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (hx : x ∈ box d n) :
    box d n ⊆ cluster d (forceOpenFinset (boxEdges d n) ω) x := by
  intro y hy
  rw [mem_cluster]
  exact box_allOpen_connected ω hx hy


theorem box_allOpen_cluster_eq {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    cluster d (forceOpenFinset (boxEdges d n) ω) x
      = cluster d (forceOpenFinset (boxEdges d n) ω) y :=
  cluster_eq_of_connected (box_allOpen_connected ω hx hy)

end Percolation
end StatMech
