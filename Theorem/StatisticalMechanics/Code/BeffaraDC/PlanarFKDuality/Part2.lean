/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part2
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


theorem pfd_faceStep (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    {f g : Site 2} (hfg : (whb_faceRegion (jei_pushGraph P K)).Adj f g) :
    (pfdClosedDual P K).Reachable (pfdFace P f) (pfdFace P g) := by
  classical
  by_cases hwall : sharedPrimalEdge f g ∈ (imageGraph P).edgeSet
  · induction hshared : sharedPrimalEdge f g using Sym2.inductionOn with
    | _ a b =>
      have hab : (imageGraph P).Adj a b := by
        rw [← SimpleGraph.mem_edgeSet]
        exact hshared ▸ hwall
      rw [imageGraph_adj] at hab
      obtain ⟨x, y, hxy, hx, hy⟩ := hab
      have hnotK : ¬ K.Adj x y := by
        intro hKxy
        apply hfg.2
        rw [hshared, SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
        refine ⟨x, y, hKxy, hx, hy⟩
      let e : kwg_Edge P := ⟨s(x, y), (SimpleGraph.mem_edgeSet P.G).mpr hxy⟩
      have heK : e.1 ∉ K.edgeSet := by
        rw [SimpleGraph.mem_edgeSet]
        exact hnotK
      have hemb : kwg_embeddedEdge P e = sharedPrimalEdge f g := by
        rw [hshared, ← hx, ← hy]
        rfl
      have hflank : s(kwg_flankLeft P e, kwg_flankRight P e) = s(f, g) :=
        (jce_sharedPrimalEdge_inj (kwg_flanks_adj P e) hfg.1).mpr
          ((kwg_flanks_shared P e).trans hemb)
      have hends : kwg_dualEnds P e = s(pfdFace P f, pfdFace P g) := by
        unfold kwg_dualEnds pfdFace
        exact congrArg (Sym2.map
          ((whb_faceRegion (imageGraph P)).connectedComponentMk)) hflank
      by_cases heq : pfdFace P f = pfdFace P g
      · simpa [heq]
      · exact (pfdClosedDual_adj P K _ _).2 ⟨heq, e, heK, hends⟩ |>.reachable
  · have hamb : (whb_faceRegion (imageGraph P)).Adj f g := ⟨hfg.1, hwall⟩
    have heq : pfdFace P f = pfdFace P g :=
      ConnectedComponent.connectedComponentMk_eq_of_adj hamb
    simpa [heq]


theorem pfd_regionReachable_to_dual (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    {f g : Site 2}
    (hfg : (whb_faceRegion (jei_pushGraph P K)).Reachable f g) :
    (pfdClosedDual P K).Reachable (pfdFace P f) (pfdFace P g) := by
  rcases hfg with ⟨w⟩
  induction w with
  | nil => exact ⟨Walk.nil⟩
  | @cons a b c hab w ih => exact (pfd_faceStep P K hab).trans ih


theorem pfd_embeddedEdge_not_mem_push (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (e : kwg_Edge P) (heK : e.1 ∉ K.edgeSet) :
    kwg_embeddedEdge P e ∉ (jei_pushGraph P K).edgeSet := by
  rcases e with ⟨e, heG⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      intro hmem
      have hadj : (jei_pushGraph P K).Adj (P.emb x) (P.emb y) := by
        rw [← SimpleGraph.mem_edgeSet]
        exact hmem
      rw [jei_pushGraph_adj] at hadj
      obtain ⟨a, b, hab, ha, hb⟩ := hadj
      have hax : a = x := P.emb.injective ha
      have hby : b = y := P.emb.injective hb
      subst a
      subst b
      exact heK ((SimpleGraph.mem_edgeSet K).mpr hab)


theorem pfd_ambientFace_le_openFace (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) :
    whb_faceRegion (imageGraph P) ≤ whb_faceRegion (jei_pushGraph P K) := by
  apply jwc_faceRegion_antitone
  rw [← jei_pushGraph_G P]
  exact jwc_pushGraph_mono P hKP


theorem pfd_dualAdj_to_regionReachable (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) {f g : Site 2}
    (hfg : (pfdClosedDual P K).Adj (pfdFace P f) (pfdFace P g)) :
    (whb_faceRegion (jei_pushGraph P K)).Reachable f g := by
  classical
  obtain ⟨_, e, heK, hends⟩ := (pfdClosedDual_adj P K _ _).mp hfg
  let R := whb_faceRegion (imageGraph P)
  let L := kwg_flankLeft P e
  let U := kwg_flankRight P e
  have hLU : (whb_faceRegion (jei_pushGraph P K)).Adj L U := by
    refine ⟨kwg_flanks_adj P e, ?_⟩
    rw [kwg_flanks_shared P e]
    exact pfd_embeddedEdge_not_mem_push P K e heK
  have hpair : s(R.connectedComponentMk L, R.connectedComponentMk U) =
      s(R.connectedComponentMk f, R.connectedComponentMk g) := by
    simpa only [R, L, U, pfdFace, kwg_dualEnds] using hends
  rw [Sym2.eq_iff] at hpair
  rcases hpair with hpair | hpair
  · have hfL : R.connectedComponentMk f = R.connectedComponentMk L := hpair.1.symm
    have hUg : R.connectedComponentMk U = R.connectedComponentMk g := hpair.2
    exact ((ConnectedComponent.eq.mp hfL).mono (pfd_ambientFace_le_openFace P K hKP)).trans
      (hLU.reachable.trans
        ((ConnectedComponent.eq.mp hUg).mono (pfd_ambientFace_le_openFace P K hKP)))
  · have hfU : R.connectedComponentMk f = R.connectedComponentMk U := hpair.2.symm
    have hLg : R.connectedComponentMk L = R.connectedComponentMk g := hpair.1
    exact ((ConnectedComponent.eq.mp hfU).mono (pfd_ambientFace_le_openFace P K hKP)).trans
      (hLU.symm.reachable.trans
        ((ConnectedComponent.eq.mp hLg).mono (pfd_ambientFace_le_openFace P K hKP)))


theorem pfd_dualWalk_to_regionReachable (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) {C D : kwg_Face P}
    (w : (pfdClosedDual P K).Walk C D) {f g : Site 2}
    (hf : pfdFace P f = C) (hg : pfdFace P g = D) :
    (whb_faceRegion (jei_pushGraph P K)).Reachable f g := by
  induction w generalizing f with
  | nil =>
      have hcomp : pfdFace P f = pfdFace P g := hf.trans hg.symm
      exact (ConnectedComponent.eq.mp hcomp).mono (pfd_ambientFace_le_openFace P K hKP)
  | @cons A B E hAB w ih =>
      have hout : pfdFace P B.out = B := by
        exact B.out_eq
      have hadj : (pfdClosedDual P K).Adj (pfdFace P f) (pfdFace P B.out) := by
        simpa only [hf, hout] using hAB
      exact (pfd_dualAdj_to_regionReachable P K hKP hadj).trans
        (ih hout hg)


theorem pfd_regionReachable_iff_dual (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) {f g : Site 2} :
    (whb_faceRegion (jei_pushGraph P K)).Reachable f g ↔
      (pfdClosedDual P K).Reachable (pfdFace P f) (pfdFace P g) := by
  constructor
  · exact pfd_regionReachable_to_dual P K
  · rintro ⟨w⟩
    exact pfd_dualWalk_to_regionReachable P K hKP w rfl rfl


end BeffaraDC
end StatMech
