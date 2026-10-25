/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualDomination
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareAnchoredShell.Part4
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualCoordinates
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

open StatMech.Universality

noncomputable section

theorem kwg_embeddedEdge_eq_sharedPrimalEdge_of_dualEnds_eq_inner
    {N m : Nat} (hNm : N < m)
    {x y : FK.boxVerts 2 N}
    (hxy : (FK.boxGraph 2 N).Adj x y)
    {e : kwg_Edge (fkSquareBoxPlanar m)}
    (he : kwg_dualEnds (fkSquareBoxPlanar m) e =
      s(fkSquareBox_innerFaceMap N m x,
        fkSquareBox_innerFaceMap N m y)) :
    kwg_embeddedEdge (fkSquareBoxPlanar m) e =
      sharedPrimalEdge x.1 y.1 := by
  have hflank :
      s(kwg_flankLeft (fkSquareBoxPlanar m) e,
          kwg_flankRight (fkSquareBoxPlanar m) e) = s(x.1, y.1) := by
    change s(pfdFace (fkSquareBoxPlanar m)
          (kwg_flankLeft (fkSquareBoxPlanar m) e),
        pfdFace (fkSquareBoxPlanar m)
          (kwg_flankRight (fkSquareBoxPlanar m) e)) =
      s(pfdFace (fkSquareBoxPlanar m) x.1,
        pfdFace (fkSquareBoxPlanar m) y.1) at he
    rw [Sym2.eq_iff] at he ⊢
    rcases he with he | he
    · exact Or.inl ⟨(pfdFace_eq_inner_iff hNm x.2).mp he.1,
        (pfdFace_eq_inner_iff hNm y.2).mp he.2⟩
    · exact Or.inr ⟨(pfdFace_eq_inner_iff hNm y.2).mp he.1,
        (pfdFace_eq_inner_iff hNm x.2).mp he.2⟩
  rw [← kwg_flanks_shared]
  exact (jce_sharedPrimalEdge_inj (kwg_flanks_adj _ e) hxy).mp hflank


theorem fkSquareDualInnerActiveRestrict_pfdSupport_eq_faceDual
    {N m : Nat} (hNm : N < m)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 m))) :
    fkSquareDualInnerActiveRestrict hNm (fkSquarePfdSupport m omega) =
      fkSquareFaceDualInnerActive N (FK.extendEdge 2 m omega) := by
  funext a
  rcases a with ⟨a, haedge⟩
  induction a using Sym2.inductionOn with
  | _ x y =>
      have hxy : (FK.boxGraph 2 N).Adj x y :=
        (SimpleGraph.mem_edgeSet _).1 haedge
      simp only [fkSquareDualInnerActiveRestrict,
        ocd_innerRestrictActive, fkSquarePfdSupport,
        pfdIndexedSupportActive, restrictActive,
        indexedBundleSupport, pfdEdgeComplement_apply,
        fkSquareFaceDualInnerActive]
      simp only [ocd_innerEdge_mk, FK.edgeIncl, Sym2.map_mk]
      rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hxy]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      constructor
      · rintro ⟨e, he, hopen⟩
        have hemb :=
          kwg_embeddedEdge_eq_sharedPrimalEdge_of_dualEnds_eq_inner
            hNm hxy he
        have hrange : sharedPrimalEdge x.1 y.1 ∈
            Set.range (FK.edgeIncl 2 m) := by
          refine ⟨e.1, ?_⟩
          simpa [kwg_embeddedEdge, fkSquareBoxPlanar_emb] using hemb
        unfold FK.extendEdge
        rw [dif_pos hrange]
        have hchoose : hrange.choose = e.1 :=
          FK.edgeIncl_injective 2 m <| by
            calc
              FK.edgeIncl 2 m hrange.choose = sharedPrimalEdge x.1 y.1 :=
                hrange.choose_spec
              _ = FK.edgeIncl 2 m e.1 := by
                simpa [kwg_embeddedEdge, fkSquareBoxPlanar_emb] using hemb.symm
        rw [hchoose]
        simpa using hopen
      · intro hopen
        have hfull : (pfdClosedDual (fkSquareBoxPlanar m) ⊥).Adj
            (fkSquareBox_innerFaceMap N m x)
            (fkSquareBox_innerFaceMap N m y) :=
          (fkSquareBox_innerFaceMap_adj hNm x y).mp hxy
        obtain ⟨e, he⟩ := pfdEdgeBundle_nonempty_of_fullDualEdge
          (fkSquareBoxPlanar m)
          ((SimpleGraph.mem_edgeSet _).2 hfull)
        rw [mem_pfdEdgeBundle] at he
        refine ⟨e, he, ?_⟩
        have hemb :=
          kwg_embeddedEdge_eq_sharedPrimalEdge_of_dualEnds_eq_inner
            hNm hxy he
        have hrange : sharedPrimalEdge x.1 y.1 ∈
            Set.range (FK.edgeIncl 2 m) := by
          refine ⟨e.1, ?_⟩
          simpa [kwg_embeddedEdge, fkSquareBoxPlanar_emb] using hemb
        unfold FK.extendEdge at hopen
        rw [dif_pos hrange] at hopen
        have hchoose : hrange.choose = e.1 :=
          FK.edgeIncl_injective 2 m <| by
            calc
              FK.edgeIncl 2 m hrange.choose = sharedPrimalEdge x.1 y.1 :=
                hrange.choose_spec
              _ = FK.edgeIncl 2 m e.1 := by
                simpa [kwg_embeddedEdge, fkSquareBoxPlanar_emb] using hemb.symm
        rwa [hchoose] at hopen


theorem fkSquare_innerEdgeLE_mem_edgeSet {R N : Nat} (hRN : R ≤ N)
    (a : (FK.boxGraph 2 R).edgeSet) :
    FK.innerEdgeLE 2 hRN a.1 ∈ (FK.boxGraph 2 N).edgeSet := by
  rcases a with ⟨a, ha⟩
  induction a using Sym2.inductionOn with
  | _ x y =>
      have hxy : (FK.boxGraph 2 R).Adj x y :=
        (SimpleGraph.mem_edgeSet _).1 ha
      rw [FK.innerEdgeLE, Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact hxy


end
end StatMech.FrontierD
