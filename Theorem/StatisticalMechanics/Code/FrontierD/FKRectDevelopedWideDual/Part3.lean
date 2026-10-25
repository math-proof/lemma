/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideDual.Part3
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectWide_faceDualExtension_horizontal_expanded
    (n : Int) (hn : 0 < n) (eta : ConfigSpace (Sym2 (Site 2)))
    (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
    HorizontalCrossing (StatMech.Universality.fci_faceDualConfig eta)
      (-1) (3 * n) 0 n := by
  obtain ⟨xb, yt, hxy⟩ :=
    fkRectWide_faceDualExtension_vertical_confined n hn eta hno
  refine ⟨⟨StatMech.Universality.crf_swap xb.1,
      (StatMech.Universality.crf_mem_bottomSide_swap
        0 n (-1) (3 * n) xb.1).mp xb.2⟩,
    ⟨StatMech.Universality.crf_swap yt.1,
      (StatMech.Universality.crf_mem_topSide_swap
        0 n (-1) (3 * n) yt.1).mp yt.2⟩, ?_⟩
  exact hxy.map (fkRectWideFaceDualSwapHom n eta)


theorem fkRectWide_faceBand_horizontalCrossing_to_rect
    {eta : ConfigSpace (Sym2 (Site 2))} {W H : Int} (hW : 0 < W)
    (h : HorizontalCrossing eta (-1) W 0 H) :
    HorizontalCrossing eta 0 W 0 H := by
  obtain ⟨xl, yr, hconn⟩ := h
  have hxlS : (xl : Site 2) ∈ rect (-1) W 0 H :=
    leftSide_subset xl.2
  have hyrS : (yr : Site 2) ∈ rect (-1) W 0 H :=
    rightSide_subset yr.2
  obtain ⟨w⟩ := hconn
  let p0 : (openSubgraph 2 eta).Walk (xl : Site 2) (yr : Site 2) :=
    w.map (SimpleGraph.Embedding.induce
      (rect (-1) W 0 H : Set (Site 2))).toHom
  let p : (openSubgraph 2 eta).Walk (yr : Site 2) (xl : Site 2) :=
    p0.reverse
  have hpsupp : ∀ z ∈ p.support,
      z ∈ (rect (-1) W 0 H : Set (Site 2)) := by
    intro z hz
    have hz0 : z ∈ p0.support := by simpa [p] using hz
    have hsupp := SimpleGraph.Walk.support_map
      (SimpleGraph.Embedding.induce
        (G := openSubgraph 2 eta)
        (rect (-1) W 0 H : Set (Site 2))).toHom w
    obtain ⟨z', hz', hz'eq⟩ := (List.mem_map).mp (hsupp ▸ hz0)
    rw [← hz'eq]
    exact z'.2
  have hyr0 : (yr : Site 2) 0 = W := yr.2.2
  have hxl0 : (xl : Site 2) 0 = -1 := xl.2.2
  obtain ⟨j, hjle, hju, hjabove⟩ :=
    StatMech.BeffaraDC.torus_walk_first_hit_down p 0 0
      (by omega) (by omega)
  let u : Site 2 := p.getVert j
  let q : (openSubgraph 2 eta).Walk (yr : Site 2) u := p.take j
  have hqsupp : ∀ z ∈ q.support,
      z ∈ (rect 0 W 0 H : Set (Site 2)) := by
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
    have hznonneg : 0 ≤ z 0 := by
      rw [hzm]
      rcases lt_or_eq_of_le hmle with hm | rfl
      · exact le_of_lt (hjabove m hm)
      · exact le_of_eq hju.symm
    omega
  have huT : u ∈ (rect 0 W 0 H : Set (Site 2)) :=
    hqsupp u q.end_mem_support
  have hyrT : (yr : Site 2) ∈ (rect 0 W 0 H : Set (Site 2)) :=
    hqsupp _ q.start_mem_support
  have hu0 : u 0 = 0 := hju
  refine ⟨⟨u, huT, hu0⟩, ⟨(yr : Site 2), hyrT, hyr0⟩, ?_⟩
  exact ⟨q.reverse.induce (rect 0 W 0 H) (by
    intro z hz
    exact hqsupp z (by simpa using hz))⟩


theorem fkRectWide_faceDualHorizontal_of_not_vertical
    (n : Int) (hn : 0 < n) (eta : ConfigSpace (Sym2 (Site 2)))
    (hno : ¬ VerticalCrossing eta 0 (3 * n) 0 n) :
    HorizontalCrossing (StatMech.Universality.fci_faceDualConfig eta)
      0 (3 * n) 0 n :=
  fkRectWide_faceBand_horizontalCrossing_to_rect (by omega)
    (fkRectWide_faceDualExtension_horizontal_expanded n hn eta hno)


theorem fkRectDevelopedThreeByOneVertex_fst_succ_lt
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {z : Site 2} (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
    (fkRectDevelopedSquareVertex R n z).1.val + 1 < R.width := by
  let t := fkRectDevelopedSquarePoint n z
  let p := fkRectSquareUndevelopPoint t
  have hp := fkRectDevelopedThreeByOne_undevelop_bounds
    R n hwidth hheight hz
  have hpoint := fkRectVertexSquarePoint_developedThreeByOneVertex
    R n hwidth hheight hz
  have hundev := congrArg fkRectSquareUndevelopPoint hpoint
  simp only [fkRectVertexSquarePoint,
    fkRectSquareUndevelopPoint_developPoint] at hundev
  have hx : ((fkRectDevelopedSquareVertex R n z).1.val : Int) = p.1 :=
    congrArg Prod.fst hundev
  change z ∈ rect 0 (3 * (n : Int)) 0 n at hz
  rw [mem_rect] at hz
  have hpUpper : p.1 < 4 * (n : Int) := by
    dsimp [p, t, fkRectDevelopedSquarePoint,
      fkRectSquareUndevelopPoint]
    omega
  exact_mod_cast (show
    ((fkRectDevelopedSquareVertex R n z).1.val : Int) + 1 < R.width by
      omega)


theorem fkRectDualEdgeToEdge_not_cut_of_developedThreeByOne
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {f g : Site 2} (hf : f ∈ fkRectDevelopedThreeByOneRect n)
    (hg : g ∈ fkRectDevelopedThreeByOneRect n)
    (d : R.EdgeIndex)
    (hedge : fkRectTorusIndexedEdge R d =
      s(fkRectDevelopedSquareVertex R n f,
        fkRectDevelopedSquareVertex R n g))
    (hd : d ∉ fkRectTorusCutEdges R) :
    fkRectDualEdgeToEdge R d ∉ fkRectTorusCutEdges R := by
  rcases d with ⟨b, x, y⟩
  cases b
  · have hxy : y.val ≠ 0 ∧ x.val ≠ 0 := by
      simpa [mem_fkRectTorusCutEdges_iff] using hd
    simpa [fkRectDualEdgeToEdge,
      mem_fkRectTorusCutEdges_iff] using hxy.1
  · have hy0 : y.val ≠ 0 := by
      simpa [mem_fkRectTorusCutEdges_iff] using hd
    have hedge' := hedge
    simp only [fkRectTorusIndexedEdge, if_pos] at hedge'
    have hxface : x = (fkRectDevelopedSquareVertex R n f).1 ∨
        x = (fkRectDevelopedSquareVertex R n g).1 := by
      rcases Sym2.eq_iff.mp hedge' with h | h
      · exact Or.inl (congrArg Prod.fst h.1)
      · exact Or.inr (congrArg Prod.fst h.1)
    have hxsucc : x.val + 1 < R.width := by
      rcases hxface with hx | hx
      · rw [hx]
        exact fkRectDevelopedThreeByOneVertex_fst_succ_lt
          R n hn hwidth hheight hf
      · rw [hx]
        exact fkRectDevelopedThreeByOneVertex_fst_succ_lt
          R n hn hwidth hheight hg
    have hsucc : (finitePeriodicSucc R.width_pos x).val = x.val + 1 := by
      rw [finitePeriodicSucc_val]
      simp [ne_of_lt hxsucc]
    rw [mem_fkRectTorusCutEdges_iff]
    simp [fkRectDualEdgeToEdge, hy0, hsucc]


theorem fkRectDevelopedThreeByOne_faceDual_adj_imp_dual_adj
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration) {f g : Site 2}
    (hf : f ∈ fkRectDevelopedThreeByOneRect n)
    (hg : g ∈ fkRectDevelopedThreeByOneRect n)
    (hfg : (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).Adj f g) :
    (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Adj
      (fkRectDevelopedSquareVertex R n f)
      (fkRectDevelopedSquareVertex R n g) := by
  rw [openSubgraph_adj] at hfg
  obtain ⟨hlat, hopen⟩ := hfg
  have hcut := fkRectDevelopedThreeByOneVertex_cutGraph_adj R n
    hwidth hheight hf hg hlat
  obtain ⟨⟨d, hedge⟩, hcutEdge⟩ :=
    (fkRectCutGraph_adj_iff R _ _).mp hcut
  have hd : d ∉ fkRectTorusCutEdges R := by
    intro hd
    apply hcutEdge
    rw [← hedge, mem_fkRectTorusCutGraphEdges]
    exact hd
  let e := fkRectDualEdgeToEdge R d
  have he : e ∉ fkRectTorusCutEdges R :=
    fkRectDualEdgeToEdge_not_cut_of_developedThreeByOne
      R n hn hwidth hheight hf hg d hedge hd
  have hde : fkRectEdgeToDualEdge R e = d := by
    simp [e]
  let dp := fkRectLiftedIndexedEdgeEnds R d
  let ep := fkRectLiftedIndexedEdgeEnds R e
  have hproject :
      s(fkRectLiftedVertex R dp.1, fkRectLiftedVertex R dp.2) =
        s(fkRectDevelopedSquareVertex R n f,
          fkRectDevelopedSquareVertex R n g) := by
    rw [← fkRectLiftedIndexedEdgeEnds_project R d]
    exact hedge
  have hsites := congrArg (Sym2.map (fkRectVertexSquareSite R)) hproject
  have hd1 :=
    fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut R d hd
  have hd2 :=
    fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut₂ R d hd
  have hsites' :
      s(fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.1),
          fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.2)) =
        s(fkRectDevelopedSquareSite n f,
          fkRectDevelopedSquareSite n g) := by
    simp only [Sym2.map_pair_eq] at hsites
    rw [fkRectVertexSquareSite_developedThreeByOneVertex
          R n hwidth hheight hf,
        fkRectVertexSquareSite_developedThreeByOneVertex
          R n hwidth hheight hg] at hsites
    change s(fkRectSquareSiteOfPair
          (fkRectVertexSquarePoint R (fkRectLiftedVertex R dp.1)),
        fkRectSquareSiteOfPair
          (fkRectVertexSquarePoint R (fkRectLiftedVertex R dp.2))) = _ at hsites
    rw [← hd1, ← hd2] at hsites
    exact hsites
  have htadj : (hypercubicLattice 2).Adj
      (fkRectDevelopedSquareSite n f)
      (fkRectDevelopedSquareSite n g) := by
    rw [hypercubicLattice_adj] at hlat ⊢
    simpa [fkRectDevelopedSquareSite, fkRectDevelopedSquarePoint,
      fkRectSquareSiteOfPair, Fin.sum_univ_two] using hlat
  have hshared :
      sharedPrimalEdge (fkRectDevelopedSquareSite n f)
          (fkRectDevelopedSquareSite n g) =
        sharedPrimalEdge
          (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.1))
          (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.2)) := by
    rcases Sym2.eq_iff.mp hsites' with h | h
    · rw [h.1, h.2]
    · rw [h.1, h.2]
      exact sharedPrimalEdge_comm_of_adj htadj
  have hcross := fkRectLiftedDualEdge_sharedPrimalEdge R e he (by
    simpa [hde] using hd)
  dsimp only at hcross
  rw [hde] at hcross
  change sharedPrimalEdge
      (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.1))
      (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.2)) =
    Sym2.map fkRectSquareSiteOfPair
      s(fkRectSquareDevelopPoint ep.1,
        fkRectSquareDevelopPoint ep.2) at hcross
  have hplane := hshared.trans hcross
  have hmapped := congrArg (Sym2.map (fkRectSquareSiteVertex R)) hplane
  rw [fkRectDevelopedSquare_sharedPrimalEdge n hlat] at hmapped
  have hedgeMap :
      Sym2.map (fkRectDevelopedSquareVertex R n)
          (sharedPrimalEdge f g) = fkRectTorusIndexedEdge R e := by
    rw [fkRectLiftedIndexedEdgeEnds_project R e]
    simpa [Sym2.map_map, Function.comp_def,
      fkRectSquareRepresentativeVertex_developPoint, ep] using hmapped
  have hpull : fkRectDevelopedSquarePullback R n omega
      (sharedPrimalEdge f g) = false := by
    rw [StatMech.Universality.fci_faceDualConfig,
      StatMech.Universality.fci_faceEdgeEquiv_mk_of_adj hlat] at hopen
    cases hval : fkRectDevelopedSquarePullback R n omega
        (sharedPrimalEdge f g) <;> simp_all
  have heclosed : omega e = false := by
    unfold fkRectDevelopedSquarePullback at hpull
    rw [hedgeMap, fkRectFullGraphConfiguration_indexedEdge] at hpull
    exact hpull
  refine ⟨d, ?_, hedge⟩
  rw [← hde, fkRectDualConfigurationEquiv_apply_edgeToDualEdge]
  simpa [heclosed]


end
end StatMech.FrontierD
