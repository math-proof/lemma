/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalGluing.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


namespace ClosedPolygonalGluingFlatSurfaceEmbedding

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


theorem sum_coneAnchor_fibers
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k : Fin p.darts.length,
      ∑ cone : {cone // cone ∈ embedding.developedConeSupport p},
        if embedding.coneAnchor p hp cone = k then
          embedding.coneOrder cone - 1 else 0) =
      ∑ cone ∈ embedding.developedConeSupport p,
        (embedding.coneOrder cone - 1) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rw [Finset.sum_comm]
  calc
    (∑ cone : {cone // cone ∈ embedding.developedConeSupport p},
        ∑ k : Fin p.darts.length,
          if embedding.coneAnchor p hp cone = k then
            embedding.coneOrder cone - 1 else 0) =
        ∑ cone : {cone // cone ∈ embedding.developedConeSupport p},
          (embedding.coneOrder cone - 1) := by simp
    _ = _ := Finset.sum_attach (embedding.developedConeSupport p)
      (fun cone => embedding.coneOrder cone - 1)


theorem chartIndexGaussBonnet
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, embedding.chartTransitionIndex p k) =
      (surfaceBaseQuadraticParity
        (surfaceSubgraphHomology embedding.edgeClass p.edges.toFinset)).val +
      2 * embedding.chartRegularTurnCorrection p +
      ∑ cone ∈ embedding.developedConeSupport p,
        (embedding.coneOrder cone - 1) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  calc
    (∑ k, embedding.chartTransitionIndex p k) =
        ∑ k, (surfaceWalkQuadraticIncrement embedding.edgeClass p k +
          2 * embedding.regularChartPairIndex p hp k +
          ∑ cone : {cone // cone ∈ embedding.developedConeSupport p},
            if embedding.coneAnchor p hp cone = k then
              embedding.coneOrder cone - 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      simp [chartTransitionIndex, hp]
    _ = (∑ k, surfaceWalkQuadraticIncrement embedding.edgeClass p k) +
        2 * (∑ k, embedding.regularChartPairIndex p hp k) +
        ∑ k, ∑ cone :
          {cone // cone ∈ embedding.developedConeSupport p},
            if embedding.coneAnchor p hp cone = k then
              embedding.coneOrder cone - 1 else 0 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
      rw [sum_surfaceWalkQuadraticIncrement embedding.edgeClass p hp,
        sum_coneAnchor_fibers embedding p hp]
      simp [chartRegularTurnCorrection, hp]


end ClosedPolygonalGluingFlatSurfaceEmbedding
end StatMech.FrontierA
