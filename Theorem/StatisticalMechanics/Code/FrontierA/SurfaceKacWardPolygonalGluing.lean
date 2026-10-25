/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardPolygonalGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalGluing
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


@[simp] theorem surfaceWalkPrefixHomology_zero {g : Nat} {V : Type u}
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root) :
    surfaceWalkPrefixHomology edgeClass p 0 = 0 := by
  simp [surfaceWalkPrefixHomology]

theorem surfaceWalkPrefixHomology_length {g : Nat} {V : Type u}
    [DecidableEq V]
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root)
    (hp : p.IsCycle) :
    surfaceWalkPrefixHomology edgeClass p p.darts.length =
      surfaceSubgraphHomology edgeClass p.edges.toFinset := by
  rw [surfaceWalkPrefixHomology, SimpleGraph.Walk.length_darts,
    <- SimpleGraph.Walk.length_edges, List.take_length]
  exact (List.sum_toFinset edgeClass hp.edges_nodup).symm


theorem sum_surfaceWalkQuadraticIncrement {g : Nat} {V : Type u}
    [DecidableEq V]
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root)
    (hp : p.IsCycle) :
    (∑ k : Fin p.darts.length,
      surfaceWalkQuadraticIncrement edgeClass p k) =
        (surfaceBaseQuadraticParity
          (surfaceSubgraphHomology edgeClass p.edges.toFinset)).val := by
  unfold surfaceWalkQuadraticIncrement
  rw [Fin.sum_univ_eq_sum_range
    (fun i => surfaceWalkQuadraticHeight edgeClass p (i + 1) -
      surfaceWalkQuadraticHeight edgeClass p i) p.darts.length]
  rw [Finset.sum_range_sub]
  simp only [surfaceWalkQuadraticHeight, surfaceWalkPrefixHomology_zero,
    surfaceBaseQuadraticParity, Prod.fst_zero, Pi.zero_apply, Prod.snd_zero,
    mul_zero, Finset.sum_const_zero, Fin.val_zero,
    Nat.cast_zero, sub_zero]
  rw [surfaceWalkPrefixHomology_length edgeClass p hp]


end StatMech.FrontierA
