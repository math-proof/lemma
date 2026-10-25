/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem eaw_no_monotone_loop (g : ℕ → ℤ) (L : ℕ) (h3 : 3 ≤ L)
    (hloop : g 0 = g L)
    (hstep : ∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1)
    (hne : g 1 ≠ g 0)
    (hinj : Set.InjOn g {i | i ≤ L - 1}) : False := by
  classical
  obtain ⟨k, hkmem, hkmax⟩ := Finset.exists_max_image (Finset.range (L + 1)) g
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨j, hjmem, hjmin⟩ := Finset.exists_min_image (Finset.range (L + 1)) g
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  rw [Finset.mem_range] at hkmem hjmem
  have machine : ∀ m, m ≤ L → (∀ i, i ≤ L → g i ≤ g m) → 0 < m → m < L → False := by
    intro m hmL hmmax hm0 hmL'
    have hs1 := hstep (m - 1) (by omega)
    have hs2 := hstep m (by omega)
    rw [show m - 1 + 1 = m by omega] at hs1
    have hle1 : g (m - 1) ≤ g m := hmmax (m - 1) (by omega)
    have hle2 : g (m + 1) ≤ g m := hmmax (m + 1) (by omega)
    have heq1 : g (m - 1) = g m - 1 := by omega
    have heq2 : g (m + 1) = g m - 1 := by omega
    by_cases hmp : m + 1 ≤ L - 1
    · have : (m - 1) = (m + 1) := hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) (by omega)
      omega
    · have hmpL : m + 1 = L := by omega
      have : g (m - 1) = g 0 := by rw [heq1, ← heq2, hmpL, ← hloop]
      have : (m - 1) = 0 := hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) this
      omega
  have machineMin : ∀ m, m ≤ L → (∀ i, i ≤ L → g m ≤ g i) → 0 < m → m < L → False := by
    intro m hmL hmmin hm0 hmL'
    have hs1 := hstep (m - 1) (by omega)
    have hs2 := hstep m (by omega)
    rw [show m - 1 + 1 = m by omega] at hs1
    have hle1 : g m ≤ g (m - 1) := hmmin (m - 1) (by omega)
    have hle2 : g m ≤ g (m + 1) := hmmin (m + 1) (by omega)
    have heq1 : g (m - 1) = g m + 1 := by omega
    have heq2 : g (m + 1) = g m + 1 := by omega
    by_cases hmp : m + 1 ≤ L - 1
    · have : (m - 1) = (m + 1) := hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) (by omega)
      omega
    · have hmpL : m + 1 = L := by omega
      have : g (m - 1) = g 0 := by rw [heq1, ← heq2, hmpL, ← hloop]
      have : (m - 1) = 0 := hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) this
      omega
  have hkmax' : ∀ i, i ≤ L → g i ≤ g k := fun i hi => hkmax i (Finset.mem_range.mpr (by omega))
  have hjmin' : ∀ i, i ≤ L → g j ≤ g i := fun i hi => hjmin i (Finset.mem_range.mpr (by omega))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hj1 : g j ≤ g 1 := hjmin' 1 (by omega)
    have hlt0 : g j < g 0 := by omega
    have hj0 : j ≠ 0 := by intro h; rw [h] at hlt0; omega
    have hjL : j ≠ L := by intro h; rw [h, ← hloop] at hlt0; omega
    exact machineMin j (by omega) hjmin' (by omega) (by omega)
  · have hk1 : g 1 ≤ g k := hkmax' 1 (by omega)
    have hgt0 : g 0 < g k := by omega
    have hk0 : k ≠ 0 := by intro h; rw [h] at hgt0; omega
    have hkL' : k ≠ L := by intro h; rw [h, ← hloop] at hgt0; omega
    exact machine k (by omega) hkmax' (by omega) (by omega)


theorem eaw_getVert_edge_mem {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {i : ℕ} (hi : i < Vc.length) :
    s(Vc.getVert i, Vc.getVert (i + 1)) ∈ Vc.edges := by
  rw [SimpleGraph.Walk.edges]
  have hidl : i < Vc.darts.length := by rw [Vc.length_darts]; exact hi
  have hmem : Vc.darts[i] ∈ Vc.darts := List.getElem_mem hidl
  have hmap := List.mem_map_of_mem (f := SimpleGraph.Dart.edge) hmem
  rwa [Vc.darts_getElem_eq_getVert i hidl] at hmap


theorem eaw_exists_vertEdge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) :
    ∃ i, i < Vc.length ∧ (Vc.getVert i) 0 = (Vc.getVert (i + 1)) 0 := by
  by_contra hcon
  push Not at hcon
  set L := Vc.length with hL
  have h3 : 3 ≤ L := hcyc.three_le_length
  have hstep1 : ∀ i, i < L → (Vc.getVert i) 1 = (Vc.getVert (i + 1)) 1 := by
    intro i hi
    have hadj := Vc.adj_getVert_succ (show i < Vc.length by rw [← hL]; exact hi)
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    have hne := hcon i hi
    omega
  have hrow : ∀ i, i ≤ L → (Vc.getVert i) 1 = a 1 := by
    intro i hi
    induction i with
    | zero => rw [Vc.getVert_zero]
    | succ n ih => have hn : n < L := by omega
                   rw [← hstep1 n hn, ih (by omega)]
  set g : ℕ → ℤ := fun i => (Vc.getVert i) 0 with hg
  apply eaw_no_monotone_loop g L h3
  · show (Vc.getVert 0) 0 = (Vc.getVert L) 0
    rw [Vc.getVert_zero]
    rw [show Vc.getVert L = a from by rw [hL]; exact Vc.getVert_length]
  · intro i hi
    have hadj := Vc.adj_getVert_succ (show i < Vc.length by rw [← hL]; exact hi)
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    have hne := hcon i hi
    have h1 := hstep1 i hi
    show (Vc.getVert (i + 1)) 0 = (Vc.getVert i) 0 + 1 ∨ (Vc.getVert (i + 1)) 0 = (Vc.getVert i) 0 - 1
    omega
  · show (Vc.getVert 1) 0 ≠ (Vc.getVert 0) 0
    have h0 := hcon 0 (by omega)
    rw [Vc.getVert_zero] at h0 ⊢
    exact fun h => h0 h.symm
  · intro n hn m hm hnm
    simp only [Set.mem_setOf_eq] at hn hm
    have hgvn : Vc.getVert n = Vc.getVert m := by
      funext t; fin_cases t
      · exact hnm
      · rw [show (⟨1, by norm_num⟩ : Fin 2) = (1 : Fin 2) from rfl, hrow n (by omega),
          hrow m (by omega)]
    exact hcyc.getVert_injOn' (show n ≤ L - 1 by simpa [hL] using hn)
      (show m ≤ L - 1 by simpa [hL] using hm) hgvn


theorem eaw_mem_edges_exists {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (h : s(x, y) ∈ Vc.edges) :
    ∃ i, i < Vc.length ∧ s(Vc.getVert i, Vc.getVert (i + 1)) = s(x, y) := by
  have hadj : Vc.toSubgraph.Adj x y := SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr h
  rw [SimpleGraph.Walk.toSubgraph_adj_iff] at hadj
  obtain ⟨i, hi, hil⟩ := hadj
  exact ⟨i, hil, hi⟩


theorem eaw_rayCount_extreme {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (c r : ℤ)
    (hmin : ∀ x y : Site 2, s(x, y) ∈ Vc.edges → x 0 = y 0 → c ≤ x 0)
    (he0 : s((![c, r] : Site 2), ![c, r + 1]) ∈ Vc.edges)
    (hnodup : Vc.edges.Nodup) :
    jec_rayCount (![c + 1, r + 1] : Site 2) Vc = 1 := by
  classical
  rw [jec_rayCount]
  have hkey : ∀ e ∈ Vc.edges,
      (decide (jec_rayEdge (![c + 1, r + 1] : Site 2) e) = true ↔
        (e == s((![c, r] : Site 2), ![c, r + 1])) = true) := by
    intro e he
    rw [decide_eq_true_eq, beq_iff_eq]
    obtain ⟨x, y⟩ := e
    have hadj : (hypercubicLattice 2).Adj x y := Vc.adj_of_mem_edges he
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    simp only [jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro ⟨⟨hcol, hle⟩, hgap⟩
      have hge : c ≤ x 0 := hmin x y he hcol
      have hx0 : x 0 = c := by omega
      have hy0 : y 0 = c := by rw [← hcol]; exact hx0
      rcases hgap with ⟨hx1, hy1⟩ | ⟨hy1, hx1⟩
      · have hx : x = (![c, r] : Site 2) := by funext i; fin_cases i <;> simp_all
        have hy : y = (![c, r + 1] : Site 2) := by funext i; fin_cases i <;> simp_all
        rw [hx, hy]
      · have hx : x = (![c, r + 1] : Site 2) := by funext i; fin_cases i <;> simp_all
        have hy : y = (![c, r] : Site 2) := by funext i; fin_cases i <;> simp_all
        rw [hx, hy, Sym2.eq_swap]
    · intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · subst hx; subst hy; exact ⟨⟨rfl, by simp⟩, Or.inl ⟨by simp, by simp⟩⟩
      · subst hx; subst hy; exact ⟨⟨rfl, by simp⟩, Or.inr ⟨by simp, by simp⟩⟩
  rw [List.countP_congr hkey, ← List.count]
  exact List.count_eq_one_of_mem hnodup he0


theorem eaw_cycle_oddCell {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) :
    ∃ z : Site 2, jec_rayCount z Vc = 1 := by
  classical
  have hnodup : Vc.edges.Nodup := hcyc.edges_nodup
  
  set C : Finset ℤ :=
    ((Finset.range Vc.length).filter
      (fun i => (Vc.getVert i) 0 = (Vc.getVert (i + 1)) 0)).image (fun i => (Vc.getVert i) 0)
    with hC
  
  obtain ⟨i0, hi0, hi0v⟩ := eaw_exists_vertEdge Vc hcyc
  have hCne : C.Nonempty := by
    refine ⟨(Vc.getVert i0) 0, ?_⟩
    rw [hC, Finset.mem_image]
    exact ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi0, hi0v⟩, rfl⟩
  set c : ℤ := C.min' hCne with hc
  
  obtain ⟨i, hiC, hic⟩ := Finset.mem_image.mp (C.min'_mem hCne)
  rw [Finset.mem_filter, Finset.mem_range] at hiC
  obtain ⟨hilen, hivert⟩ := hiC
  
  have hadj := Vc.adj_getVert_succ hilen
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have hcol_i : (Vc.getVert i) 0 = c := hic
  have hcol_i1 : (Vc.getVert (i + 1)) 0 = c := by rw [← hivert]; exact hic
  
  have hrows : (Vc.getVert (i + 1)) 1 = (Vc.getVert i) 1 + 1 ∨
      (Vc.getVert (i + 1)) 1 = (Vc.getVert i) 1 - 1 := by
    rw [hcol_i, hcol_i1] at hadj; omega
  
  have hmin : ∀ x y : Site 2, s(x, y) ∈ Vc.edges → x 0 = y 0 → c ≤ x 0 := by
    intro x y hxy hxy0
    obtain ⟨j, hj, hje⟩ := eaw_mem_edges_exists Vc hxy
    
    rw [Sym2.eq_iff] at hje
    have hjvert : (Vc.getVert j) 0 = (Vc.getVert (j + 1)) 0 := by
      rcases hje with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hxy0
      · rw [h1, h2]; exact hxy0.symm
    have hjmemC : (Vc.getVert j) 0 ∈ C := by
      rw [hC, Finset.mem_image]
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hjvert⟩, rfl⟩
    have hcle : c ≤ (Vc.getVert j) 0 := C.min'_le _ hjmemC
    
    rcases hje with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [← h1]; exact hcle
    · rw [← h2, ← hjvert]; exact hcle
  
  rcases hrows with hup | hdown
  · 
    set r : ℤ := (Vc.getVert i) 1 with hr
    have hlow : Vc.getVert i = (![c, r] : Site 2) := by
      funext t; fin_cases t
      · simpa using hcol_i
      · show (Vc.getVert i) 1 = r; rw [hr]
    have hhigh : Vc.getVert (i + 1) = (![c, r + 1] : Site 2) := by
      funext t; fin_cases t
      · simpa using hcol_i1
      · show (Vc.getVert (i + 1)) 1 = r + 1
        rw [hup, hr]
    have he0 : s((![c, r] : Site 2), ![c, r + 1]) ∈ Vc.edges := by
      rw [← hlow, ← hhigh]; exact eaw_getVert_edge_mem Vc hilen
    exact ⟨![c + 1, r + 1], eaw_rayCount_extreme Vc c r hmin he0 hnodup⟩
  · 
    set r : ℤ := (Vc.getVert (i + 1)) 1 with hr
    have hlow : Vc.getVert (i + 1) = (![c, r] : Site 2) := by
      funext t; fin_cases t
      · simpa using hcol_i1
      · show (Vc.getVert (i + 1)) 1 = r; rw [hr]
    have hhigh : Vc.getVert i = (![c, r + 1] : Site 2) := by
      funext t; fin_cases t
      · simpa using hcol_i
      · show (Vc.getVert i) 1 = r + 1
        rw [hr]; omega
    have he0 : s((![c, r] : Site 2), ![c, r + 1]) ∈ Vc.edges := by
      rw [Sym2.eq_swap, ← hlow, ← hhigh]; exact eaw_getVert_edge_mem Vc hilen
    exact ⟨![c + 1, r + 1], eaw_rayCount_extreme Vc c r hmin he0 hnodup⟩


theorem eaw_cycle_oddCell' {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) :
    ∃ z : Site 2, ¬ Even (jec_rayCount z Vc) := by
  obtain ⟨z, hz⟩ := eaw_cycle_oddCell Vc hcyc
  exact ⟨z, by rw [hz]; decide⟩


end Lattice
end StatMech
