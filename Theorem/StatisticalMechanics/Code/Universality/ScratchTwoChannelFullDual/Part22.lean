/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part26
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelIndexedSpoke_le_open {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelIndexedSpokeGraph gamma gamma' ≤
      rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega := by
  intro x y hxy
  rw [rlc_twoChannelIndexedOuterOpenGraph, FK.openSub_adj]
  refine ⟨Or.inr hxy, ?_⟩
  exact rlc_twoChannelIndexedOuterConfig_spoke gamma gamma' omega
    ((SimpleGraph.mem_edgeSet _).mpr hxy)


theorem rlc_twoChannelIndexedOuterEdge_open_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈
        (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).edgeSet ↔
      f.1 ∉ (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).edgeSet := by
  rw [rlc_twoChannelIndexedOuterOpenGraph]
  induction hxy : rlc_twoChannelIndexedOuterEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      have hrandom :
          (rlc_twoChannelIndexedRandomGraph gamma gamma').Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, ← hxy]
        exact rlc_twoChannelIndexedOuterEdge_mem_random gamma gamma' f
      have hconfig :=
        rlc_twoChannelIndexedOuterConfig_randomEdge gamma gamma' omega f
      rw [hxy] at hconfig
      rw [hconfig]
      constructor
      · rintro ⟨_, hopen⟩ hprimal
        have htrue : rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1 = true := by
          induction hfedge : f.1 using Sym2.inductionOn with
          | _ u v =>
              rw [hfedge] at hprimal
              rw [SimpleGraph.mem_edgeSet, FK.openSub_adj] at hprimal
              simpa [hfedge] using hprimal.2
        rw [htrue] at hopen
        simp at hopen
      · intro hclosed
        refine ⟨Or.inl hrandom, ?_⟩
        have hfalse : rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1 = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hopen
          apply hclosed
          induction hfedge : f.1 using Sym2.inductionOn with
          | _ u v =>
              have hfmem : f.1 ∈
                  (rlc_connectorTwoChannelAugmentedPlanarDomain
                    gamma gamma').G.edgeSet := f.2
              rw [hfedge] at hfmem
              rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
              exact ⟨(SimpleGraph.mem_edgeSet _).mp hfmem,
                by simpa [hfedge] using hopen⟩
        simp [hfalse]

theorem rlc_twoChannelIndexedOuterEdge_endpoints_not_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'))
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : rlc_twoChannelIndexedOuterEdge gamma gamma' f = s(x, y)) :
    ¬RlcTwoChannelIndexedIsFace gamma gamma' x ∧
      ¬RlcTwoChannelIndexedIsFace gamma gamma' y := by
  have htag := rlc_twoChannelIndexedFaceTag_outerEdge gamma gamma' f
  rw [hxy, Sym2.map_mk, Sym2.eq_iff] at htag
  have hxfalse : rlc_twoChannelIndexedFaceTag gamma gamma' x = false := by
    rcases htag with htag | htag <;> exact htag.1
  have hyfalse : rlc_twoChannelIndexedFaceTag gamma gamma' y = false := by
    rcases htag with htag | htag <;> exact htag.2
  constructor
  · intro hx
    have hxtrue := (rlc_twoChannelIndexedFaceTag_eq_true_iff
      gamma gamma' x).2 hx
    simp [hxtrue] at hxfalse
  · intro hy
    have hytrue := (rlc_twoChannelIndexedFaceTag_eq_true_iff
      gamma gamma' y).2 hy
    simp [hytrue] at hyfalse


theorem rlc_twoChannelIndexedFaceProjection_reachable_of_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : (rlc_twoChannelIndexedOuterOpenGraph
      gamma gamma' omega).Adj x y) :
    (BeffaraDC.pfdClosedDual
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable
      (rlc_twoChannelIndexedFaceProjection gamma gamma' x)
      (rlc_twoChannelIndexedFaceProjection gamma gamma' y) := by
  rw [rlc_twoChannelIndexedOuterOpenGraph, FK.openSub_adj] at hxy
  rcases hxy.1 with hrandom | hspoke
  · obtain ⟨f, hf⟩ := hrandom.2
    have hopen : rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈
        (rlc_twoChannelIndexedOuterOpenGraph
          gamma gamma' omega).edgeSet := by
      rw [hf]
      exact (SimpleGraph.mem_edgeSet _).mpr <| by
        rw [rlc_twoChannelIndexedOuterOpenGraph, FK.openSub_adj]
        exact ⟨Or.inl hrandom, hxy.2⟩
    have habsent := (rlc_twoChannelIndexedOuterEdge_open_iff
      gamma gamma' omega f).1 hopen
    have hends : Ising.kwg_dualEnds
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f =
        s(rlc_twoChannelIndexedFaceProjection gamma gamma' x,
          rlc_twoChannelIndexedFaceProjection gamma gamma' y) := by
      rw [← rlc_twoChannelIndexedFaceProjection_outerEdge
        gamma gamma' f, hf, Sym2.map_mk]
    by_cases heq : rlc_twoChannelIndexedFaceProjection gamma gamma' x =
        rlc_twoChannelIndexedFaceProjection gamma gamma' y
    · rw [heq]
    · exact ((BeffaraDC.pfdClosedDual_adj
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) _ _).2
          ⟨heq, f, habsent, hends⟩).reachable
  · rw [hspoke.2.1]

theorem rlc_twoChannelIndexedFaceProjection_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : (rlc_twoChannelIndexedOuterOpenGraph
      gamma gamma' omega).Reachable x y) :
    (BeffaraDC.pfdClosedDual
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable
      (rlc_twoChannelIndexedFaceProjection gamma gamma' x)
      (rlc_twoChannelIndexedFaceProjection gamma gamma' y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail hreach hadj ih =>
      exact ih.trans
        (rlc_twoChannelIndexedFaceProjection_reachable_of_adj
          gamma gamma' omega hadj)


theorem rlc_twoChannelIndexedFace_reachable_of_pfd_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {C D : Ising.kwg_Face
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')}
    (hCD : (BeffaraDC.pfdClosedDual
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Adj C D) :
    (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
      (rlc_twoChannelIndexedOuterFace gamma gamma' C)
      (rlc_twoChannelIndexedOuterFace gamma gamma' D) := by
  rw [BeffaraDC.pfdClosedDual_adj] at hCD
  obtain ⟨_, f, habsent, hends⟩ := hCD
  have hopen := (rlc_twoChannelIndexedOuterEdge_open_iff
    gamma gamma' omega f).2 habsent
  induction hedge : rlc_twoChannelIndexedOuterEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      have hnonface := rlc_twoChannelIndexedOuterEdge_endpoints_not_face
        gamma gamma' f hedge
      have hxface := (rlc_twoChannelIndexedSpoke_le_open gamma gamma' omega
        (rlc_twoChannelIndexedSpoke_adj_face
          gamma gamma' x hnonface.1)).reachable
      have hyface := (rlc_twoChannelIndexedSpoke_le_open gamma gamma' omega
        (rlc_twoChannelIndexedSpoke_adj_face
          gamma gamma' y hnonface.2)).reachable
      have hxy : (rlc_twoChannelIndexedOuterOpenGraph
          gamma gamma' omega).Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, ← hedge]
        exact hopen
      have hproj :
          s(rlc_twoChannelIndexedFaceProjection gamma gamma' x,
            rlc_twoChannelIndexedFaceProjection gamma gamma' y) = s(C, D) := by
        rw [← hends,
          ← rlc_twoChannelIndexedFaceProjection_outerEdge gamma gamma' f,
          hedge, Sym2.map_mk]
      rw [Sym2.eq_iff] at hproj
      rcases hproj with hproj | hproj
      · simpa [hproj.1, hproj.2] using
          hxface.symm.trans (hxy.reachable.trans hyface)
      · simpa [hproj.1, hproj.2] using
          hyface.symm.trans (hxy.symm.reachable.trans hxface)


theorem rlc_twoChannelIndexedFace_reachable_of_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {C D : Ising.kwg_Face
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')}
    (hCD : (BeffaraDC.pfdClosedDual
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable
            C D) :
    (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
      (rlc_twoChannelIndexedOuterFace gamma gamma' C)
      (rlc_twoChannelIndexedOuterFace gamma gamma' D) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hCD
  induction hCD with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail hreach hadj ih =>
      exact ih.trans (rlc_twoChannelIndexedFace_reachable_of_pfd_adj
        gamma gamma' omega hadj)


theorem rlc_twoChannelIndexedOuter_reachable_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (x : RlcTwoChannelIndexedOuterVertex gamma gamma') :
    (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable x
      (rlc_twoChannelIndexedOuterFace gamma gamma'
        (rlc_twoChannelIndexedFaceProjection gamma gamma' x)) := by
  by_cases hx : RlcTwoChannelIndexedIsFace gamma gamma' x
  · have heq : x = rlc_twoChannelIndexedOuterFace gamma gamma'
        (rlc_twoChannelIndexedFaceProjection gamma gamma' x) := by
      rcases x with x | (x | x)
      · simp [RlcTwoChannelIndexedIsFace] at hx
      · simp [RlcTwoChannelIndexedIsFace] at hx
      · rfl
    rw [heq]
    rw [rlc_twoChannelIndexedFaceProjection_face]
  · exact (rlc_twoChannelIndexedSpoke_le_open gamma gamma' omega
      (rlc_twoChannelIndexedSpoke_adj_face gamma gamma' x hx)).reachable


theorem rlc_twoChannelIndexedOuter_reachable_iff_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (x y : RlcTwoChannelIndexedOuterVertex gamma gamma') :
    (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable x y ↔
      (BeffaraDC.pfdClosedDual
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable
        (rlc_twoChannelIndexedFaceProjection gamma gamma' x)
        (rlc_twoChannelIndexedFaceProjection gamma gamma' y) := by
  constructor
  · exact rlc_twoChannelIndexedFaceProjection_reachable
      gamma gamma' omega
  · intro hxy
    exact (rlc_twoChannelIndexedOuter_reachable_face
      gamma gamma' omega x).trans
      ((rlc_twoChannelIndexedFace_reachable_of_pfd
        gamma gamma' omega hxy).trans
        (rlc_twoChannelIndexedOuter_reachable_face
          gamma gamma' omega y).symm)


theorem rlc_twoChannelIndexedOuterTargets_reachable_of_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (x y : RlcConnectorVertex n)
    (hxy : (BeffaraDC.pfdClosedDual
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable
      (BeffaraDC.pfdFace
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (rlc_dualReflect.symm x.1))
      (BeffaraDC.pfdFace
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (rlc_dualReflect.symm y.1))) :
    (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
      (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
      (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
  exact (rlc_twoChannelIndexedOuter_reachable_face gamma gamma' omega
      (rlc_twoChannelIndexedOuterTarget gamma gamma' x)).trans
    ((rlc_twoChannelIndexedFace_reachable_of_pfd gamma gamma' omega hxy).trans
      (rlc_twoChannelIndexedOuter_reachable_face gamma gamma' omega
        (rlc_twoChannelIndexedOuterTarget gamma gamma' y)).symm)

theorem rlc_twoChannelIndexedOuterConfig_closedSource_randomEdge_iff
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedOuterConfig gamma gamma' (fun _ => false)
        (rlc_twoChannelIndexedOuterEdge gamma gamma' f) = true ↔
      f.1 ∉ (rlc_connectorTraceWiring gamma gamma').edgeSet := by
  rw [rlc_twoChannelIndexedOuterConfig_randomEdge]
  induction hedge : f.1 using Sym2.inductionOn with
  | _ x y =>
      have hfmem := f.2
      rw [hedge, SimpleGraph.mem_edgeSet] at hfmem
      change (rlc_connectorTwoChannelGraph gamma gamma' ⊔
        rlc_connectorTraceWiring gamma gamma').Adj x y at hfmem
      rcases hfmem with htwo | htrace
      · have hnotTrace : s(x, y) ∉
            (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
          intro hmem
          exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp
            (SimpleGraph.mem_edgeFinset.mp hmem))
        have hforce : rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' (fun _ => false))
            s(x, y) = false := by
          change (if s(x, y) ∈
              (rlc_connectorTraceWiring gamma gamma').edgeFinset then
            true else rlc_twoChannelEdgeConfigExtend gamma gamma'
              (fun _ => false) s(x, y)) = false
          calc
            _ = rlc_twoChannelEdgeConfigExtend gamma gamma'
                (fun _ => false) s(x, y) := if_neg hnotTrace
            _ = false := by
              change (if _ : s(x, y) ∈
                  (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
                false else false) = false
              split <;> rfl
        have hnotSet : s(x, y) ∉
            (rlc_connectorTraceWiring gamma gamma').edgeSet := by
          intro hmem
          exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp hmem)
        constructor
        · intro _
          exact hnotSet
        · intro _
          calc
            (!(rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma'
                  (fun _ => false)) s(x, y))) = (!false) :=
              congrArg Bool.not hforce
            _ = true := rfl
      · have htraceMem : s(x, y) ∈
            (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr
            ((SimpleGraph.mem_edgeSet _).mpr htrace)
        have hforce : rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' (fun _ => false))
            s(x, y) = true := by
          unfold rlc_connectorForceTraceConfig
          exact if_pos htraceMem
        have hset : s(x, y) ∈
            (rlc_connectorTraceWiring gamma gamma').edgeSet :=
          (SimpleGraph.mem_edgeSet _).mpr htrace
        constructor
        · intro hopen
          have himpossible : (!true) = true :=
            (congrArg Bool.not hforce).symm.trans hopen
          exact Bool.noConfusion himpossible
        · intro hnot
          exact (hnot hset).elim


theorem rlc_twoChannelIndexedOuterConfig_variable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    rlc_twoChannelIndexedOuterConfig gamma gamma' omega
        (target.1.map (rlc_twoChannelIndexedOuterTarget gamma gamma')) =
      rlc_twoChannelFullDualConfig gamma gamma' omega target.1 := by
  rw [← rlc_twoChannelIndexedOuterEdge_variable target,
    rlc_twoChannelIndexedOuterConfig_randomEdge,
    ← rlc_twoChannelFullAmbientDual_reflectedEdge gamma gamma' omega
      (rlc_twoChannelIndexedAugmentedEdge target)]
  rw [rlc_twoChannelFullDualConfig]
  change rlc_dualReflectConfig
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
        (rlc_twoChannelReflectedDualEdge gamma gamma'
          (rlc_twoChannelIndexedAugmentedEdge target)) =
    rlc_dualReflectConfig
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
        (target.1.map Subtype.val)
  rw [rlc_twoChannelIndexedAugmentedEdge_reflected]

theorem rlc_twoChannelIndexedRandomGraph_adj_target {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    (rlc_twoChannelIndexedRandomGraph gamma gamma').Adj
        (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
        (rlc_twoChannelIndexedOuterTarget gamma gamma' y) ↔
      (rlc_twoChannelFullVariableGraph gamma gamma').Adj x y := by
  constructor
  · rintro ⟨_, f, hf⟩
    unfold rlc_twoChannelIndexedOuterEdge at hf
    split at hf
    · rename_i hret
      have hedge : hret.choose.1 = s(x, y) := by
        apply Sym2.map.injective
          (rlc_twoChannelIndexedOuterTarget_injective gamma gamma')
        simpa [Sym2.map_mk] using hf
      rw [← SimpleGraph.mem_edgeSet, ← hedge]
      exact hret.choose.2
    · rw [Sym2.eq_iff] at hf
      simp [rlc_twoChannelIndexedOuterTarget,
        rlc_twoChannelIndexedOuterPort] at hf
  · intro hxy
    let target : RlcTwoChannelFullVariableTargetEdge gamma gamma' :=
      ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hxy⟩
    let source := rlc_twoChannelFullSourceEdge target
    let f : Ising.kwg_Edge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
      ⟨source.1, SimpleGraph.edgeSet_mono le_sup_left source.2⟩
    have hreflected : rlc_twoChannelReflectedDualEdge gamma gamma' f =
        target.1.map Subtype.val := by
      apply rlc_pimsEdgeEquiv.injective
      rw [rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge]
      change (rlc_twoChannelFullSourceEdge target).1.map Subtype.val =
        rlc_pimsEdgeEquiv (target.1.map Subtype.val)
      exact rlc_twoChannelFullSourceEdge_map target
    have hret : RlcTwoChannelIndexedRetainedEdge gamma gamma' f :=
      ⟨target, hreflected.symm⟩
    refine ⟨fun h => hxy.1.ne
      (rlc_twoChannelIndexedOuterTarget_injective gamma gamma' h), f, ?_⟩
    unfold rlc_twoChannelIndexedOuterEdge
    rw [dif_pos hret]
    have hedge : hret.choose.1 = target.1 := by
      apply Sym2.map.injective Subtype.val_injective
      exact hret.choose_spec.trans hreflected
    rw [hedge]
    rfl

theorem rlc_twoChannelIndexedSpokeGraph_not_adj_targets {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    ¬(rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj
      (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
      (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
  rintro ⟨_, _, hghost⟩
  simp [RlcTwoChannelIndexedIsFace,
    rlc_twoChannelIndexedOuterTarget] at hghost

theorem rlc_twoChannelIndexedOuter_adjMatch {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.ocd_AdjMatch (rlc_twoChannelFullVariableGraph gamma gamma')
      (rlc_twoChannelIndexedOuterGraph gamma gamma')
      (rlc_twoChannelIndexedOuterTarget gamma gamma') := by
  intro x y
  rw [rlc_twoChannelIndexedOuterGraph, SimpleGraph.sup_adj]
  constructor
  · intro hxy
    exact Or.inl
      ((rlc_twoChannelIndexedRandomGraph_adj_target gamma gamma' x y).2 hxy)
  · rintro (hrandom | hspoke)
    · exact (rlc_twoChannelIndexedRandomGraph_adj_target gamma gamma' x y).1
        hrandom
    · exact (rlc_twoChannelIndexedSpokeGraph_not_adj_targets
        gamma gamma' x y hspoke).elim


theorem rlc_twoChannelIndexed_condProb_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')))
    (eta : ConfigSpace
      (Sym2 (RlcConnectorVertex n))) :
    FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_innerEdgeFinset
          (rlc_twoChannelIndexedOuterTarget gamma gamma')) psi
        (FK.ocd_psiExt
          (rlc_twoChannelIndexedOuterTarget gamma gamma') psi eta) =
      FK.bcProb (rlc_twoChannelFullVariableGraph gamma gamma')
        (FK.ocd_inducedWiring
          (rlc_twoChannelIndexedOuterGraph gamma gamma')
          (rlc_twoChannelIndexedOuterTarget gamma gamma')
          (fun _ => False) psi) p q eta := by
  simpa using
    (FK.ocd_condBcProb_psiExt_eq_bcProb
      (Gin := rlc_twoChannelFullVariableGraph gamma gamma')
      (Gout := rlc_twoChannelIndexedOuterGraph gamma gamma')
      (ιV := rlc_twoChannelIndexedOuterTarget gamma gamma')
      (bdryOut := fun _ => False)
      (rlc_twoChannelIndexedOuterTarget_injective gamma gamma')
      (rlc_twoChannelIndexedOuter_adjMatch gamma gamma')
      hp hp1 hq psi eta)

end
end StatMech.Universality
