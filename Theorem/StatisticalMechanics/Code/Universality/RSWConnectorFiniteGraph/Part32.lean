/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part19
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorOuterSpoke_le_open {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorOuterSpokeGraph gamma gamma' ≤
      rlc_connectorOuterOpenGraph gamma gamma' tau := by
  intro x y hxy
  rw [rlc_connectorOuterOpenGraph, FK.openSub_adj]
  refine ⟨Or.inr hxy, ?_⟩
  apply rlc_connectorOuterDualConfig_spoke gamma gamma' tau
  exact (SimpleGraph.mem_edgeSet _).mpr hxy


theorem rlc_connectorOuterDualEdge_open_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterDualEdge gamma gamma' f ∈
        (rlc_connectorOuterOpenGraph gamma gamma' tau).edgeSet ↔
      f.1 ∉ (FK.openSub
        (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet := by
  rw [rlc_connectorOuterOpenGraph]
  induction hxy : rlc_connectorOuterDualEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      have hrandom :
          (rlc_connectorOuterRandomGraph gamma gamma').Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, ← hxy]
        exact rlc_connectorOuterDualEdge_mem_random gamma gamma' f
      have hconfig :=
        rlc_connectorOuterDualConfig_randomEdge gamma gamma' tau f
      rw [hxy] at hconfig
      rw [hconfig]
      constructor
      · rintro ⟨_, hopen⟩ hprimal
        have htrue :
            rlc_connectorForceTraceConfig gamma gamma' tau f.1 = true := by
          induction hfedge : f.1 using Sym2.inductionOn with
          | _ u v =>
              rw [hfedge] at hprimal
              rw [SimpleGraph.mem_edgeSet, FK.openSub_adj] at hprimal
              simpa [hfedge] using hprimal.2
        rw [htrue] at hopen
        simp at hopen
      · intro hclosed
        refine ⟨Or.inl hrandom, ?_⟩
        have hfalse :
            rlc_connectorForceTraceConfig gamma gamma' tau f.1 = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hopen
          apply hclosed
          induction hfedge : f.1 using Sym2.inductionOn with
          | _ u v =>
              have hfmem : f.1 ∈
                  (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeSet :=
                f.2
              rw [hfedge] at hfmem
              rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
              exact ⟨(SimpleGraph.mem_edgeSet _).mp hfmem,
                by simpa [hfedge] using hopen⟩
        simp [hfalse]


theorem rlc_connectorOuterFaceProjection_reachable_of_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : RlcConnectorOuterDualVertex gamma gamma'}
    (hxy : (rlc_connectorOuterOpenGraph gamma gamma' tau).Adj x y) :
    (BeffaraDC.pfdClosedDual
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable
      (rlc_connectorOuterFaceProjection gamma gamma' x)
      (rlc_connectorOuterFaceProjection gamma gamma' y) := by
  rw [rlc_connectorOuterOpenGraph, FK.openSub_adj] at hxy
  rcases hxy.1 with hrandom | hspoke
  · obtain ⟨f, hf⟩ := hrandom.2
    have hopen : rlc_connectorOuterDualEdge gamma gamma' f ∈
        (rlc_connectorOuterOpenGraph gamma gamma' tau).edgeSet := by
      rw [hf]
      exact (SimpleGraph.mem_edgeSet _).mpr <| by
        rw [rlc_connectorOuterOpenGraph, FK.openSub_adj]
        exact ⟨Or.inl hrandom, hxy.2⟩
    have habsent := (rlc_connectorOuterDualEdge_open_iff
      gamma gamma' tau f).1 hopen
    have hends : Ising.kwg_dualEnds
          (rlc_connectorAugmentedPlanarDomain gamma gamma') f =
        s(rlc_connectorOuterFaceProjection gamma gamma' x,
          rlc_connectorOuterFaceProjection gamma gamma' y) := by
      rw [← rlc_connectorOuterFaceProjection_edge gamma gamma' f, hf,
        Sym2.map_mk]
    by_cases heq : rlc_connectorOuterFaceProjection gamma gamma' x =
        rlc_connectorOuterFaceProjection gamma gamma' y
    · rw [heq]
    · exact ((BeffaraDC.pfdClosedDual_adj
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau)) _ _).2
          ⟨heq, f, habsent, hends⟩).reachable
  · rw [hspoke.2.1]


theorem rlc_connectorOuterFaceProjection_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : RlcConnectorOuterDualVertex gamma gamma'}
    (hxy : (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable x y) :
    (BeffaraDC.pfdClosedDual
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable
      (rlc_connectorOuterFaceProjection gamma gamma' x)
      (rlc_connectorOuterFaceProjection gamma gamma' y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail hreach hadj ih =>
      exact ih.trans
        (rlc_connectorOuterFaceProjection_reachable_of_adj
          gamma gamma' tau hadj)


theorem rlc_connectorOuterDualEdge_endpoints_not_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma'))
    {x y : RlcConnectorOuterDualVertex gamma gamma'}
    (hxy : rlc_connectorOuterDualEdge gamma gamma' f = s(x, y)) :
    ¬RlcConnectorOuterIsFace gamma gamma' x ∧
      ¬RlcConnectorOuterIsFace gamma gamma' y := by
  have htag := rlc_connectorOuterFaceTag_outerDualEdge gamma gamma' f
  rw [hxy, Sym2.map_mk, Sym2.eq_iff] at htag
  have hxfalse : rlc_connectorOuterFaceTag gamma gamma' x = false := by
    rcases htag with htag | htag <;> exact htag.1
  have hyfalse : rlc_connectorOuterFaceTag gamma gamma' y = false := by
    rcases htag with htag | htag <;> exact htag.2
  constructor
  · intro hx
    have hxtrue := (rlc_connectorOuterFaceTag_eq_true_iff
      gamma gamma' x).2 hx
    simp [hxtrue] at hxfalse
  · intro hy
    have hytrue := (rlc_connectorOuterFaceTag_eq_true_iff
      gamma gamma' y).2 hy
    simp [hytrue] at hyfalse


theorem rlc_connectorOuterFace_reachable_of_pfd_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {C D : Ising.kwg_Face
      (rlc_connectorAugmentedPlanarDomain gamma gamma')}
    (hCD : (BeffaraDC.pfdClosedDual
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau))).Adj C D) :
    (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable
      (rlc_connectorOuterFace gamma gamma' C)
      (rlc_connectorOuterFace gamma gamma' D) := by
  rw [BeffaraDC.pfdClosedDual_adj] at hCD
  obtain ⟨_, f, habsent, hends⟩ := hCD
  have hopen := (rlc_connectorOuterDualEdge_open_iff
    gamma gamma' tau f).2 habsent
  induction hedge : rlc_connectorOuterDualEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      have hnonface := rlc_connectorOuterDualEdge_endpoints_not_face
        gamma gamma' f hedge
      have hxface := (rlc_connectorOuterSpoke_le_open gamma gamma' tau
        (rlc_connectorOuterSpoke_adj_face gamma gamma' x hnonface.1)).reachable
      have hyface := (rlc_connectorOuterSpoke_le_open gamma gamma' tau
        (rlc_connectorOuterSpoke_adj_face gamma gamma' y hnonface.2)).reachable
      have hxy : (rlc_connectorOuterOpenGraph gamma gamma' tau).Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, ← hedge]
        exact hopen
      have hproj :
          s(rlc_connectorOuterFaceProjection gamma gamma' x,
            rlc_connectorOuterFaceProjection gamma gamma' y) = s(C, D) := by
        rw [← hends, ← rlc_connectorOuterFaceProjection_edge gamma gamma' f,
          hedge, Sym2.map_mk]
      rw [Sym2.eq_iff] at hproj
      rcases hproj with hproj | hproj
      · simpa [hproj.1, hproj.2] using
          hxface.symm.trans (hxy.reachable.trans hyface)
      · simpa [hproj.1, hproj.2] using
          hyface.symm.trans (hxy.symm.reachable.trans hxface)


theorem rlc_connectorOuterFace_reachable_of_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {C D : Ising.kwg_Face
      (rlc_connectorAugmentedPlanarDomain gamma gamma')}
    (hCD : (BeffaraDC.pfdClosedDual
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable C D) :
    (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable
      (rlc_connectorOuterFace gamma gamma' C)
      (rlc_connectorOuterFace gamma gamma' D) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hCD
  induction hCD with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail hreach hadj ih =>
      exact ih.trans (rlc_connectorOuterFace_reachable_of_pfd_adj
        gamma gamma' tau hadj)


theorem rlc_connectorOuter_reachable_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (x : RlcConnectorOuterDualVertex gamma gamma') :
    (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable x
      (rlc_connectorOuterFace gamma gamma'
        (rlc_connectorOuterFaceProjection gamma gamma' x)) := by
  by_cases hx : RlcConnectorOuterIsFace gamma gamma' x
  · have heq : x = rlc_connectorOuterFace gamma gamma'
        (rlc_connectorOuterFaceProjection gamma gamma' x) := by
      rcases x with x | (x | x)
      · simp [RlcConnectorOuterIsFace] at hx
      · simp [RlcConnectorOuterIsFace] at hx
      · rfl
    rw [heq]
    rw [rlc_connectorOuterFaceProjection_face]
  · exact (rlc_connectorOuterSpoke_le_open gamma gamma' tau
      (rlc_connectorOuterSpoke_adj_face gamma gamma' x hx)).reachable


theorem rlc_connectorOuter_reachable_iff_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (x y : RlcConnectorOuterDualVertex gamma gamma') :
    (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable x y ↔
      (BeffaraDC.pfdClosedDual
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable
        (rlc_connectorOuterFaceProjection gamma gamma' x)
        (rlc_connectorOuterFaceProjection gamma gamma' y) := by
  constructor
  · exact rlc_connectorOuterFaceProjection_reachable gamma gamma' tau
  · intro hxy
    exact (rlc_connectorOuter_reachable_face gamma gamma' tau x).trans
      ((rlc_connectorOuterFace_reachable_of_pfd gamma gamma' tau hxy).trans
        (rlc_connectorOuter_reachable_face gamma gamma' tau y).symm)


end
end StatMech.Universality
