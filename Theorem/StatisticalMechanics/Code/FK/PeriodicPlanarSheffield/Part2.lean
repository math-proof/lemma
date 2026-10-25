/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlaneEmbedding.fundamentalArcDisplacements_isCompact
    (E : PeriodicPlaneEmbedding P) :
    IsCompact E.fundamentalArcDisplacements := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  letI : DecidableRel P.graph.Adj := Classical.decRel _
  unfold PeriodicPlaneEmbedding.fundamentalArcDisplacements
  apply Finset.isCompact_biUnion
  intro u hu
  apply Finset.isCompact_biUnion
  intro y hy
  split_ifs with h
  · simpa only [Set.image_univ] using isCompact_univ.image
      (E.coordinates.continuous.comp
        ((E.edgeArc h).continuous.sub continuous_const))
  · exact isCompact_empty


theorem PeriodicPlaneEmbedding.exists_edgeArc_displacement_bound
    (E : PeriodicPlaneEmbedding P) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  letI : DecidableRel P.graph.Adj := Classical.decRel _
  obtain ⟨R, hR⟩ :=
    E.fundamentalArcDisplacements_isCompact.isBounded.subset_closedBall
      (0 : Fin 2 → ℝ)
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro x y hxy t i
  obtain ⟨z, u, hu, hzu⟩ := P.covers x
  subst x
  let u₀ := P.shift (-z) (P.shift z u)
  let y₀ := P.shift (-z) y
  have hback : u₀ = u := by
    have h := P.shift_add z (-z) u
    rw [add_neg_cancel, P.shift_zero] at h
    exact (show P.shift (-z) (P.shift z u) = u from h.symm)
  have hu₀ : u₀ ∈ P.fundamentalDomain := by simpa only [hback] using hu
  let hbackEdge : P.graph.Adj u₀ y₀ :=
    (P.shift_adj (-z) (P.shift z u) y).2 hxy
  have ht : E.edgeArc hxy t + E.period (-z) ∈
      Set.range (E.edgeArc hbackEdge) := by
    have hrhs : E.edgeArc hxy t + E.period (-z) ∈
        (fun p => p + E.period (-z)) '' Set.range (E.edgeArc hxy) :=
      ⟨E.edgeArc hxy t, ⟨t, rfl⟩, rfl⟩
    rw [← E.edgeArc_shift (-z) hxy] at hrhs
    simpa only using hrhs
  obtain ⟨s, hs⟩ := ht
  have hdisp :
      E.coordinates (E.edgeArc hxy t - E.vertex (P.shift z u)) =
        E.coordinates (E.edgeArc hbackEdge s - E.vertex u₀) := by
    apply congrArg E.coordinates
    calc
      E.edgeArc hxy t - E.vertex (P.shift z u) =
          E.edgeArc hxy t - (E.vertex u + E.period z) :=
        congrArg (E.edgeArc hxy t - ·) (E.vertex_shift z u)
      _ = (E.edgeArc hxy t + E.period (-z)) - E.vertex u := by
        rw [map_neg]
        abel
      _ = E.edgeArc hbackEdge s - E.vertex u := by rw [hs]
      _ = E.edgeArc hbackEdge s - E.vertex u₀ :=
        congrArg (E.edgeArc hbackEdge s - ·)
          (congrArg E.vertex hback).symm
  have hmem : E.coordinates (E.edgeArc hbackEdge s - E.vertex u₀) ∈
      E.fundamentalArcDisplacements := by
    unfold PeriodicPlaneEmbedding.fundamentalArcDisplacements
    apply Set.mem_iUnion.2
    refine ⟨u₀, Set.mem_iUnion.2 ⟨hu₀, ?_⟩⟩
    apply Set.mem_iUnion.2
    refine ⟨y₀, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact (SimpleGraph.mem_neighborFinset P.graph u₀ y₀).2 hbackEdge
    · rw [dif_pos hbackEdge]
      exact ⟨s, rfl⟩
  have hnorm := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hnorm
  rw [hdisp]
  have hi : |E.coordinates (E.edgeArc hbackEdge s - E.vertex u₀) i| ≤
      ‖E.coordinates (E.edgeArc hbackEdge s - E.vertex u₀)‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (E.coordinates (E.edgeArc hbackEdge s - E.vertex u₀)) i
  exact hi.trans (hnorm.trans (le_max_left _ _))


end StatMech.FK.PeriodicPlanar
