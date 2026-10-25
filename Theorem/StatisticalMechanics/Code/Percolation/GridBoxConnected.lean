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
import Def.StatisticalMechanics.Code.Percolation.GridBoxConnected
open Set
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


lemma mk_mem_boxEdges {n : ℕ} {x y : Site d}
    (hx : x ∈ box d n) (hy : y ∈ box d n) (hadj : (hypercubicLattice d).Adj x y) :
    s(x, y) ∈ boxEdges d n := by
  classical
  unfold boxEdges
  rw [Finset.mem_image]
  refine ⟨(x, y), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, ?_⟩, hadj⟩ <;>
    · simp only [boxFinsetBK, Set.Finite.mem_toFinset]; assumption


lemma mem_boxEdges_iff {n : ℕ} {x y : Site d} :
    s(x, y) ∈ boxEdges d n ↔
      x ∈ box d n ∧ y ∈ box d n ∧ (hypercubicLattice d).Adj x y := by
  classical
  constructor
  · intro h
    unfold boxEdges at h
    rw [Finset.mem_image] at h
    obtain ⟨⟨a, b⟩, hab, he⟩ := h
    rw [Finset.mem_filter, Finset.mem_product] at hab
    rcases hab with ⟨⟨ha, hb⟩, hadj⟩
    simp only [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simpa [boxFinsetBK] using ha,
        by simpa [boxFinsetBK] using hb, hadj⟩
    · exact ⟨by simpa [boxFinsetBK] using hb,
        by simpa [boxFinsetBK] using ha, hadj.symm⟩
  · rintro ⟨hx, hy, hxy⟩
    exact mk_mem_boxEdges hx hy hxy


lemma adj_forceOpen_boxEdges {n : ℕ} (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hx : x ∈ box d n) (hy : y ∈ box d n) (hadj : (hypercubicLattice d).Adj x y) :
    (openSubgraph d (forceOpenFinset (boxEdges d n) ω)).Adj x y := by
  rw [openSubgraph_adj]
  exact ⟨hadj, forceOpenFinset_of_mem (mk_mem_boxEdges hx hy hadj) ω⟩


lemma update_mem_box {n : ℕ} {x : Site d} (hx : x ∈ box d n) (j : Fin d) {a : ℤ}
    (ha : a.natAbs ≤ n) : Function.update x j a ∈ box d n := by
  intro i
  by_cases hij : i = j
  · subst hij; rwa [Function.update_self]
  · rw [Function.update_of_ne hij]; exact hx i


lemma connected_update_ascend {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (hx : x ∈ box d n) (j : Fin d) :
    ∀ (k : ℕ) (a : ℤ), a.natAbs ≤ n → (a + (k : ℤ)).natAbs ≤ n →
      Connected d (forceOpenFinset (boxEdges d n) ω)
        (Function.update x j a) (Function.update x j (a + (k : ℤ))) := by
  set ω' := forceOpenFinset (boxEdges d n) ω with hω'
  intro k
  induction k with
  | zero => intro a _ _; simpa using connected_rfl
  | succ m ih =>
    intro a ha hak
    
    have hint : (a + (m : ℤ)).natAbs ≤ n := by
      have h1 := ha; have h2 := hak; push_cast at h2 ⊢; omega
    have hstep : Connected d ω' (Function.update x j (a + (m : ℤ)))
        (Function.update x j (a + (m : ℤ) + 1)) := by
      refine SimpleGraph.Adj.reachable
        (adj_forceOpen_boxEdges ω (update_mem_box hx j hint)
          (update_mem_box hx j ?_) (adj_update_succ x j (a + (m : ℤ))))
      have : a + (m : ℤ) + 1 = a + ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this]; exact hak
    have hrec := (ih a ha hint).trans hstep
    have he : a + (m : ℤ) + 1 = a + ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [he] at hrec


lemma connected_update {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (hx : x ∈ box d n) (j : Fin d) {a : ℤ} (ha : a.natAbs ≤ n) :
    Connected d (forceOpenFinset (boxEdges d n) ω) x (Function.update x j a) := by
  have hxj : (x j).natAbs ≤ n := hx j
  have hxupd : Function.update x j (x j) = x := Function.update_eq_self j x
  rcases le_total (x j) a with hle | hle
  · 
    obtain ⟨k, hk⟩ := Int.le.dest hle
    subst hk
    have hconn := connected_update_ascend ω hx j k (x j) hxj ha
    rwa [hxupd] at hconn
  · 
    obtain ⟨k, hk⟩ := Int.le.dest hle
    have hconn := connected_update_ascend ω hx j k a ha (by rw [hk]; exact hxj)
    rw [hk, hxupd] at hconn
    exact hconn.symm


end Percolation
end StatMech
