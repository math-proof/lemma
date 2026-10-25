/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCounterexample
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part6
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.RSW.Box

open StatMech.Universality


theorem torus_walk_first_hit_down
    {eta : ConfigSpace (Sym2 (Site 2))} {x y : Site 2}
    (p : (openSubgraph 2 eta).Walk x y) (i : Fin 2) (t : ℤ)
    (hx : t < x i) (hy : y i ≤ t) :
    ∃ j ≤ p.length, (p.getVert j) i = t ∧
      ∀ m < j, t < (p.getVert m) i := by
  have hlen : (p.getVert p.length) i ≤ t := by
    rw [p.getVert_length]
    exact hy
  classical
  let P : ℕ → Prop := fun m => (p.getVert m) i ≤ t
  have hPex : ∃ m, P m := ⟨p.length, hlen⟩
  let j := Nat.find hPex
  have hjP : (p.getVert j) i ≤ t := Nat.find_spec hPex
  have hjle : j ≤ p.length := Nat.find_le hlen
  have habove : ∀ m < j, t < (p.getVert m) i := by
    intro m hm
    have := Nat.find_min hPex hm
    simpa [P, not_le] using this
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, p.getVert_zero] at hjP
    exact (not_le_of_gt hx) hjP
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hkj : k < j := by omega
  have hkt : t < (p.getVert k) i := habove k hkj
  have hklt : k < p.length := by omega
  have hadj := p.adj_getVert_succ hklt
  have hdiff := bxa_adj_coord_diff_le hadj.1 i
  have habs : |(p.getVert k) i - (p.getVert (k + 1)) i| ≤ 1 := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hdiff
  have hge : t ≤ (p.getVert (k + 1)) i := by
    have hstep : (p.getVert k) i - (p.getVert (k + 1)) i ≤ 1 :=
      (le_abs_self _).trans habs
    omega
  refine ⟨j, hjle, ?_, habove⟩
  have hjP' : (p.getVert k.succ) i ≤ t := by
    simpa [hk] using hjP
  have hge' : t ≤ (p.getVert k.succ) i := by
    simpa [Nat.succ_eq_add_one] using hge
  rw [hk]
  exact le_antisymm hjP' hge'


theorem torus_faceBand_verticalCrossing_to_square
    {eta : ConfigSpace (Sym2 (Site 2))} {n : ℤ} (hn : 0 < n)
    (h : VerticalCrossing eta 0 (n - 1) (-1) n) :
    VerticalCrossing eta 0 n 0 n := by
  obtain ⟨xb, yt, hconn⟩ := h
  have hxbS : (xb : Site 2) ∈ rect 0 (n - 1) (-1) n := bottomSide_subset xb.2
  have hytS : (yt : Site 2) ∈ rect 0 (n - 1) (-1) n := topSide_subset yt.2
  obtain ⟨w⟩ := hconn
  let p0 : (openSubgraph 2 eta).Walk (xb : Site 2) (yt : Site 2) :=
    w.map (SimpleGraph.Embedding.induce (rect 0 (n - 1) (-1) n)).toHom
  let p : (openSubgraph 2 eta).Walk (yt : Site 2) (xb : Site 2) := p0.reverse
  have hpsupp : ∀ z ∈ p.support, z ∈ rect 0 (n - 1) (-1) n := by
    intro z hz
    have hz0 : z ∈ p0.support := by simpa [p] using hz
    have hsupp := SimpleGraph.Walk.support_map
      (SimpleGraph.Embedding.induce (rect 0 (n - 1) (-1) n)).toHom w
    obtain ⟨z', hz', hz'eq⟩ := (List.mem_map).mp (hsupp ▸ hz0)
    rw [← hz'eq]
    exact z'.2
  have hyt1 : (yt : Site 2) 1 = n := yt.2.2
  have hxb1 : (xb : Site 2) 1 = -1 := xb.2.2
  obtain ⟨j, hjle, hju, hjabove⟩ :=
    torus_walk_first_hit_down p 1 0 (by omega) (by omega)
  let u : Site 2 := p.getVert j
  let q : (openSubgraph 2 eta).Walk (yt : Site 2) u := p.take j
  have hqsupp : ∀ z ∈ q.support, z ∈ rect 0 n 0 n := by
    intro z hz
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ] at hz
    have hzp : z ∈ p.support := List.mem_of_mem_take hz
    have hzS := hpsupp z hzp
    obtain ⟨m, hmlt, hmz⟩ := List.mem_iff_getElem.mp hz
    rw [List.length_take] at hmlt
    have hmle : m ≤ j := by omega
    have hjp : j ≤ p.length := hjle
    have hzm : z = p.getVert m := by
      have hmplen : m ≤ p.length := hmle.trans hjp
      rw [List.getElem_take] at hmz
      rw [← hmz, ← SimpleGraph.Walk.getVert_eq_support_getElem p hmplen]
    rw [mem_rect] at hzS ⊢
    have hznonneg : 0 ≤ z 1 := by
      rw [hzm]
      rcases lt_or_eq_of_le hmle with hm | rfl
      · exact le_of_lt (hjabove m hm)
      · exact le_of_eq hju.symm
    omega
  have huT : u ∈ rect 0 n 0 n := hqsupp u q.end_mem_support
  have hytT : (yt : Site 2) ∈ rect 0 n 0 n := hqsupp _ q.start_mem_support
  have hu1 : u 1 = 0 := hju
  refine ⟨⟨u, huT, hu1⟩, ⟨(yt : Site 2), hytT, hyt1⟩, ?_⟩
  exact ⟨(q.reverse.induce (rect 0 n 0 n) (by
    intro z hz
    exact hqsupp z (by simpa using hz)))⟩


theorem torusReduceSwapSite_mem_square (L n : ℕ) (hnL : n < L)
    {x : Site 2} (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ)) :
    torusReduceSwapSite L x ∈ torusSquareVertexSet L n := by
  have h := torusReduceSite_mem_square L n hnL hx
  exact ⟨h.2, h.1⟩

end StatMech.BeffaraDC
