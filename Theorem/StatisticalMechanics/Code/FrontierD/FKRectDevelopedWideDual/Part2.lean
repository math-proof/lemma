/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideDual.Part2
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectWideExteriorOpenExtension_not_horizontal
    (n : Int) (hn : 0 < n) (eta : ConfigSpace (Sym2 (Site 2)))
    (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
    ¬ HorizontalCrossing (fkRectWideExteriorOpenExtension n eta)
      0 (3 * n) 0 (3 * n) := by
  intro hwide
  have hnarrow : HorizontalCrossing
      (fkRectWideExteriorOpenExtension n eta) 0 n 0 (3 * n) :=
    StatMech.Universality.bxa_horizontalCrossing_mono_width
      hn (by omega) hwide
  obtain ⟨x, y, hxy⟩ := hnarrow
  have hswap : HorizontalCrossing
      (StatMech.Universality.crf_swapConfig eta) 0 n 0 (3 * n) := by
    refine ⟨⟨x.1, x.2⟩, ⟨y.1, y.2⟩, ?_⟩
    exact hxy.map (fkRectWideExteriorOpenExtensionToSwapHom n eta)
  exact hno (StatMech.Universality.crf_horizontal_to_vertical
    0 (3 * n) 0 n eta hswap)


theorem fkRectWide_faceDualExtension_sharedPrimalEdge_mem
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))).Adj f g) :
    sharedPrimalEdge f g ∈ StatMech.Percolation.edgesWithinFinset
      (fkRectWideTallFinset n) := by
  rw [openSubgraph_adj] at hfg
  obtain ⟨hadj, hopen⟩ := hfg
  rw [StatMech.Universality.fci_faceDualConfig,
    StatMech.Universality.fci_faceEdgeEquiv_mk_of_adj hadj] at hopen
  by_contra he
  simp [fkRectWideExteriorOpenExtension, he] at hopen

theorem fkRectWide_endpoint_mem_tall_of_edge_mem
    (n : Int) {e : Sym2 (Site 2)}
    (he : e ∈ StatMech.Percolation.edgesWithinFinset
      (fkRectWideTallFinset n)) {z : Site 2} (hz : z ∈ e) :
    z ∈ fkRectWideTallFinset n := by
  rw [StatMech.Percolation.mem_edgesWithinFinset] at he
  obtain ⟨x, hx, y, hy, rfl⟩ := he
  rw [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hx
  · exact hy


theorem fkRectWide_faceDualExtension_adj_fst_le
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))).Adj f g) :
    f 0 ≤ n ∧ g 0 ≤ n := by
  have he := fkRectWide_faceDualExtension_sharedPrimalEdge_mem n eta hfg
  have hf : f = ![f 0, f 1] := by
    funext i
    fin_cases i <;> simp
  rw [hf] at hfg he ⊢
  rcases StatMech.Universality.crr_face_nbr_cases
      (f 0) (f 1) g hfg.1 with hg | hg | hg | hg <;> subst g
  · have hz := fkRectWide_endpoint_mem_tall_of_edge_mem n he
        (show faceCorner10 (f 0) (f 1) ∈
          sharedPrimalEdge ![f 0, f 1] ![f 0 + 1, f 1] by
            rw [sharedPrimalEdge_right]
            simp)
    have hz' : f 0 + 1 ≤ n := by
      have := (show faceCorner10 (f 0) (f 1) ∈
        (rect 0 n 0 (3 * n) : Set (Site 2)) by
          simpa [fkRectWideTallFinset] using hz)
      simpa [faceCorner10, mem_rect] using this.2.1
    simp only [Matrix.cons_val_zero]
    omega
  · have hz := fkRectWide_endpoint_mem_tall_of_edge_mem n he
        (show faceCorner00 (f 0) (f 1) ∈
          sharedPrimalEdge ![f 0, f 1] ![f 0 - 1, f 1] by
            rw [sharedPrimalEdge_left]
            simp)
    have hz' : f 0 ≤ n := by
      have := (show faceCorner00 (f 0) (f 1) ∈
        (rect 0 n 0 (3 * n) : Set (Site 2)) by
          simpa [fkRectWideTallFinset] using hz)
      simpa [faceCorner00, mem_rect] using this.2.1
    simp only [Matrix.cons_val_zero]
    omega
  · have hz := fkRectWide_endpoint_mem_tall_of_edge_mem n he
        (show faceCorner01 (f 0) (f 1) ∈
          sharedPrimalEdge ![f 0, f 1] ![f 0, f 1 + 1] by
            rw [sharedPrimalEdge_top]
            simp)
    have hz' : f 0 ≤ n := by
      have := (show faceCorner01 (f 0) (f 1) ∈
        (rect 0 n 0 (3 * n) : Set (Site 2)) by
          simpa [fkRectWideTallFinset] using hz)
      simpa [faceCorner01, mem_rect] using this.2.1
    simp only [Matrix.cons_val_zero]
    exact ⟨hz', hz'⟩
  · have hz := fkRectWide_endpoint_mem_tall_of_edge_mem n he
        (show faceCorner00 (f 0) (f 1) ∈
          sharedPrimalEdge ![f 0, f 1] ![f 0, f 1 - 1] by
            rw [sharedPrimalEdge_bottom]
            simp)
    have hz' : f 0 ≤ n := by
      have := (show faceCorner00 (f 0) (f 1) ∈
        (rect 0 n 0 (3 * n) : Set (Site 2)) by
          simpa [fkRectWideTallFinset] using hz)
      simpa [faceCorner00, mem_rect] using this.2.1
    simp only [Matrix.cons_val_zero]
    exact ⟨hz', hz'⟩


theorem fkRectWide_faceDualExtension_vertical_band
    (n : Int) (hn : 0 < n) (eta : ConfigSpace (Sym2 (Site 2)))
    (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
    VerticalCrossing
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))
      0 (3 * n - 1) (-1) (3 * n) := by
  exact StatMech.Universality.crr_square_compl_subset_faceDualRect_unconditional
    (3 * n) (by omega)
      (fkRectWideExteriorOpenExtension_not_horizontal n hn eta hno)


theorem fkRectWide_faceDualExtension_vertical_confined
    (n : Int) (hn : 0 < n) (eta : ConfigSpace (Sym2 (Site 2)))
    (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
    VerticalCrossing
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))
      0 n (-1) (3 * n) := by
  let xi := StatMech.Universality.fci_faceDualConfig
    (fkRectWideExteriorOpenExtension n eta)
  obtain ⟨xb, yt, hconn⟩ :=
    fkRectWide_faceDualExtension_vertical_band n hn eta hno
  obtain ⟨w⟩ := hconn
  have hne : (xb : Site 2) ≠ (yt : Site 2) := by
    intro heq
    have hcoord := congrFun heq 1
    have hxb : (xb : Site 2) 1 = -1 := xb.2.2
    have hyt : (yt : Site 2) 1 = 3 * n := yt.2.2
    omega
  have hnonnil : ¬ w.Nil := SimpleGraph.Walk.not_nil_of_ne (by
    intro heq
    exact hne (congrArg Subtype.val heq))
  let emb := SimpleGraph.Embedding.induce (G := openSubgraph 2 xi)
    (rect 0 (3 * n - 1) (-1) (3 * n) : Set (Site 2))
  let p : (openSubgraph 2 xi).Walk (xb : Site 2) (yt : Site 2) :=
    w.map emb.toHom
  have hpsupp : ∀ z ∈ p.support,
      z ∈ (rect 0 n (-1) (3 * n) : Set (Site 2)) := by
    intro z hz
    have hsupp := SimpleGraph.Walk.support_map emb.toHom w
    obtain ⟨z', hz', rfl⟩ := (List.mem_map).mp (hsupp ▸ hz)
    have hzOld := z'.2
    have hzEdge :=
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
        (p := w) (w := z') hnonnil).mp hz'
    obtain ⟨e, he, hze⟩ := hzEdge
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy := w.adj_of_mem_edges he
        change (openSubgraph 2 xi).Adj (x : Site 2) (y : Site 2) at hxy
        have hle := fkRectWide_faceDualExtension_adj_fst_le n eta hxy
        simp only [Sym2.mem_iff] at hze
        rw [mem_rect] at hzOld ⊢
        rcases hze with rfl | rfl
        · exact ⟨hzOld.1, hle.1, hzOld.2.2.1, hzOld.2.2.2⟩
        · exact ⟨hzOld.1, hle.2, hzOld.2.2.1, hzOld.2.2.2⟩
  have hxbNew : (xb : Site 2) ∈
      (rect 0 n (-1) (3 * n) : Set (Site 2)) :=
    hpsupp _ p.start_mem_support
  have hytNew : (yt : Site 2) ∈
      (rect 0 n (-1) (3 * n) : Set (Site 2)) :=
    hpsupp _ p.end_mem_support
  refine ⟨⟨xb, hxbNew, xb.2.2⟩, ⟨yt, hytNew, yt.2.2⟩, ?_⟩
  exact ⟨p.induce (rect 0 n (-1) (3 * n)) hpsupp⟩


theorem fkRectWide_faceDualExtension_adj_swap
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))).Adj f g) :
    (openSubgraph 2 (StatMech.Universality.fci_faceDualConfig eta)).Adj
      (StatMech.Universality.crf_swap f)
      (StatMech.Universality.crf_swap g) := by
  rw [openSubgraph_adj] at hfg ⊢
  have hadjTarget :=
    (StatMech.Universality.crf_adj_swap f g).mp hfg.1
  refine ⟨hadjTarget, ?_⟩
  rw [StatMech.Universality.fci_faceDualConfig,
    StatMech.Universality.fci_faceEdgeEquiv_mk_of_adj hadjTarget]
  have hopen := hfg.2
  rw [StatMech.Universality.fci_faceDualConfig,
    StatMech.Universality.fci_faceEdgeEquiv_mk_of_adj hfg.1] at hopen
  have he := fkRectWide_faceDualExtension_sharedPrimalEdge_mem n eta
    (show (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectWideExteriorOpenExtension n eta))).Adj f g from hfg)
  rw [fkRectWideExteriorOpenExtension_eq_swap_of_mem n eta he,
    StatMech.Universality.crf_swapConfig_apply] at hopen
  have hf : f = ![f 0, f 1] := by
    funext i
    fin_cases i <;> simp
  rw [hf] at hfg hopen ⊢
  rcases StatMech.Universality.crr_face_nbr_cases
      (f 0) (f 1) g hfg.1 with hg | hg | hg | hg <;> subst g
  · simpa [sharedPrimalEdge_right, sharedPrimalEdge_top,
      faceCorner10, faceCorner11, faceCorner01,
      StatMech.Universality.crf_swap,
      StatMech.Universality.crf_swapFun] using hopen
  · simpa [sharedPrimalEdge_left, sharedPrimalEdge_bottom,
      faceCorner00, faceCorner01, faceCorner10,
      StatMech.Universality.crf_swap,
      StatMech.Universality.crf_swapFun] using hopen
  · simpa [sharedPrimalEdge_top, sharedPrimalEdge_right,
      faceCorner01, faceCorner11, faceCorner10,
      StatMech.Universality.crf_swap,
      StatMech.Universality.crf_swapFun] using hopen
  · simpa [sharedPrimalEdge_bottom, sharedPrimalEdge_left,
      faceCorner00, faceCorner10, faceCorner01,
      StatMech.Universality.crf_swap,
      StatMech.Universality.crf_swapFun] using hopen


end
end StatMech.FrontierD
