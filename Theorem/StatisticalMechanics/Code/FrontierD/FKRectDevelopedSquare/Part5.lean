/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalDualQuasiInvariant.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part5
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDevelopedSquare_compl_subset_faceDualVertical
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n) :
    (fkRectDevelopedSquareHorizontalCrossingEvent R n)ᶜ ⊆
      fkRectDevelopedSquareFaceDualVerticalEvent R n := by
  intro omega hno
  have hband : StatMech.RSW.Box.VerticalCrossing
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))
      0 ((n : Int) - 1) (-1) n := by
    exact StatMech.Universality.crr_square_compl_subset_faceDualRect_unconditional
      (n : Int) (by omega) hno
  exact StatMech.BeffaraDC.torus_faceBand_verticalCrossing_to_square
    (by omega) hband


theorem fkRectDevelopedSquare_faceDual_adj_imp_dual_adj
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration) {f g : Site 2}
    (hf : f ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hg : g ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hfg : (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).Adj f g) :
    (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Adj
      (fkRectDevelopedSquareVertex R n f)
      (fkRectDevelopedSquareVertex R n g) := by
  rw [openSubgraph_adj] at hfg
  obtain ⟨hlat, hopen⟩ := hfg
  have hcut := fkRectDevelopedSquareVertex_cutGraph_adj R n
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
    fkRectDualEdgeToEdge_not_cut_of_developedSquare R n hn
      hwidth hheight hf hg d hedge hd
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
    rw [fkRectVertexSquareSite_developedSquareVertex R n
          hwidth hheight hf,
        fkRectVertexSquareSite_developedSquareVertex R n
          hwidth hheight hg] at hsites
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
