/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part7
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
import Instance.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceEmbedding
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

theorem fkSquareBox_innerFaceMap_adj
    {N m : Nat} (hNm : N < m) (x y : FK.boxVerts 2 N) :
    (FK.boxGraph 2 N).Adj x y ↔
      (fkSquareBoxFullDualGraph m).Adj
        (fkSquareBox_innerFaceMap N m x)
        (fkSquareBox_innerFaceMap N m y) := by
  let P := fkSquareBoxPlanar m
  constructor
  · intro hxy
    have hwall : sharedPrimalEdge x.1 y.1 ∈ (imageGraph P).edgeSet :=
      sharedPrimalEdge_mem_fkSquareBoxPlanar_of_inner hNm x.2 hxy
    induction hshared : sharedPrimalEdge x.1 y.1 using Sym2.inductionOn with
    | _ a b =>
        have habImage : (imageGraph P).Adj a b := by
          rw [← SimpleGraph.mem_edgeSet]
          exact hshared ▸ hwall
        rw [imageGraph_adj] at habImage
        obtain ⟨u, v, huv, hua, hvb⟩ := habImage
        let e : kwg_Edge P :=
          ⟨s(u, v), (SimpleGraph.mem_edgeSet P.G).mpr huv⟩
        have hemb : kwg_embeddedEdge P e = sharedPrimalEdge x.1 y.1 := by
          rw [hshared, ← hua, ← hvb]
          rfl
        have hflank : s(kwg_flankLeft P e, kwg_flankRight P e) =
            s(x.1, y.1) :=
          (jce_sharedPrimalEdge_inj (kwg_flanks_adj P e) hxy).mpr
            ((kwg_flanks_shared P e).trans hemb)
        have hends : kwg_dualEnds P e =
            s(pfdFace P x.1, pfdFace P y.1) := by
          unfold kwg_dualEnds pfdFace
          exact congrArg
            (Sym2.map
              ((whb_faceRegion (imageGraph P)).connectedComponentMk))
            hflank
        have hne : pfdFace P x.1 ≠ pfdFace P y.1 := by
          intro heq
          exact hxy.ne (Subtype.ext
            ((pfdFace_eq_inner_iff hNm y.2).mp heq))
        rw [fkSquareBoxFullDualGraph, pfdClosedDual_adj]
        exact ⟨hne, e, by simp, hends⟩
  · intro hxy
    rw [fkSquareBoxFullDualGraph, pfdClosedDual_adj] at hxy
    obtain ⟨_, e, _, hends⟩ := hxy
    change s(pfdFace (fkSquareBoxPlanar m) (kwg_flankLeft (fkSquareBoxPlanar m) e),
        pfdFace (fkSquareBoxPlanar m) (kwg_flankRight (fkSquareBoxPlanar m) e)) =
      s(pfdFace (fkSquareBoxPlanar m) x.1,
        pfdFace (fkSquareBoxPlanar m) y.1) at hends
    rw [Sym2.eq_iff] at hends
    rcases hends with hends | hends
    · have hL : kwg_flankLeft (fkSquareBoxPlanar m) e = x.1 :=
        (pfdFace_eq_inner_iff hNm x.2).mp hends.1
      have hR : kwg_flankRight (fkSquareBoxPlanar m) e = y.1 :=
        (pfdFace_eq_inner_iff hNm y.2).mp hends.2
      simpa [hL, hR] using kwg_flanks_adj (fkSquareBoxPlanar m) e
    · have hL : kwg_flankLeft (fkSquareBoxPlanar m) e = y.1 :=
        (pfdFace_eq_inner_iff hNm y.2).mp hends.1
      have hR : kwg_flankRight (fkSquareBoxPlanar m) e = x.1 :=
        (pfdFace_eq_inner_iff hNm x.2).mp hends.2
      exact (by simpa [hL, hR] using
        (kwg_flanks_adj (fkSquareBoxPlanar m) e).symm)


theorem fkSquareBox_innerFaceMap_adjMatch
    {N m : Nat} (hNm : N < m) :
    ocd_AdjMatch (FK.boxGraph 2 N) (fkSquareBoxFullDualGraph m)
      (fkSquareBox_innerFaceMap N m) :=
  fkSquareBox_innerFaceMap_adj hNm


theorem fkSquareBox_boundary_of_outsideGraph_adj
    {N m : Nat} (hNm : N < m) (hN : 1 ≤ N)
    (psi : ConfigSpace (Sym2 (kwg_Face (fkSquareBoxPlanar m))))
    {x : FK.boxVerts 2 N} {z : kwg_Face (fkSquareBoxPlanar m)}
    (h : (ocd_outsideGraph (fkSquareBoxFullDualGraph m)
      (fkSquareBox_innerFaceMap N m) (fun _ => False) psi).Adj
        (fkSquareBox_innerFaceMap N m x) z) :
    FK.boxBoundary 2 N x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hrange⟩ | ⟨_, hxfalse, _⟩
  · rw [FK.boxBoundary, mem_vertexBoundary]
    refine ⟨x.2, ?_⟩
    intro hxinner
    rw [fkSquareBoxFullDualGraph, pfdClosedDual_adj] at hadj
    obtain ⟨_, e, _, hends⟩ := hadj
    change s(pfdFace (fkSquareBoxPlanar m)
        (kwg_flankLeft (fkSquareBoxPlanar m) e),
        pfdFace (fkSquareBoxPlanar m)
          (kwg_flankRight (fkSquareBoxPlanar m) e)) =
      s(pfdFace (fkSquareBoxPlanar m) x.1, z) at hends
    rw [Sym2.eq_iff] at hends
    rcases hends with hends | hends
    · have hL : kwg_flankLeft (fkSquareBoxPlanar m) e = x.1 :=
        (pfdFace_eq_inner_iff hNm x.2).mp hends.1
      have hxy : (hypercubicLattice 2).Adj x.1
          (kwg_flankRight (fkSquareBoxPlanar m) e) := by
        simpa [hL] using kwg_flanks_adj (fkSquareBoxPlanar m) e
      have hy : kwg_flankRight (fkSquareBoxPlanar m) e ∈ box 2 N := by
        have := ccb_adj_mem_box_succ hxy hxinner
        simpa [Nat.sub_add_cancel hN] using this
      let y : FK.boxVerts 2 N :=
        ⟨kwg_flankRight (fkSquareBoxPlanar m) e, hy⟩
      have hz : fkSquareBox_innerFaceMap N m y = z := by
        simpa [fkSquareBox_innerFaceMap, y] using hends.2
      apply hrange
      refine ⟨s(x, y), ?_⟩
      rw [ocd_innerEdge_mk, hz]
    · have hR : kwg_flankRight (fkSquareBoxPlanar m) e = x.1 :=
        (pfdFace_eq_inner_iff hNm x.2).mp hends.2
      have hxy : (hypercubicLattice 2).Adj x.1
          (kwg_flankLeft (fkSquareBoxPlanar m) e) := by
        simpa [hR] using (kwg_flanks_adj (fkSquareBoxPlanar m) e).symm
      have hy : kwg_flankLeft (fkSquareBoxPlanar m) e ∈ box 2 N := by
        have := ccb_adj_mem_box_succ hxy hxinner
        simpa [Nat.sub_add_cancel hN] using this
      let y : FK.boxVerts 2 N :=
        ⟨kwg_flankLeft (fkSquareBoxPlanar m) e, hy⟩
      have hz : fkSquareBox_innerFaceMap N m y = z := by
        simpa [fkSquareBox_innerFaceMap, y] using hends.1
      apply hrange
      refine ⟨s(x, y), ?_⟩
      rw [ocd_innerEdge_mk, hz]
  · exact hxfalse.elim


theorem fkSquareBox_inducedWiring_le_boundaryClique
    {N m : Nat} (hNm : N < m) (hN : 1 ≤ N)
    (psi : ConfigSpace (Sym2 (kwg_Face (fkSquareBoxPlanar m)))) :
    ocd_inducedWiring (fkSquareBoxFullDualGraph m)
        (fkSquareBox_innerFaceMap N m) (fun _ => False) psi ≤
      boundaryCliqueGraph (FK.boxBoundary 2 N) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : fkSquareBox_innerFaceMap N m x ≠
        fkSquareBox_innerFaceMap N m y :=
      fun heq => hne (fkSquareBox_innerFaceMap_injective hNm heq)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact fkSquareBox_boundary_of_outsideGraph_adj hNm hN psi hadj
  · have hreach' :
        (ocd_outsideGraph (fkSquareBoxFullDualGraph m)
          (fkSquareBox_innerFaceMap N m) (fun _ => False) psi).Reachable
            (fkSquareBox_innerFaceMap N m y)
            (fkSquareBox_innerFaceMap N m x) := hreach.symm
    have hne' : fkSquareBox_innerFaceMap N m y ≠
        fkSquareBox_innerFaceMap N m x :=
      fun heq => hne (fkSquareBox_innerFaceMap_injective hNm heq).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact fkSquareBox_boundary_of_outsideGraph_adj hNm hN psi hadj

end
end StatMech.FrontierD
