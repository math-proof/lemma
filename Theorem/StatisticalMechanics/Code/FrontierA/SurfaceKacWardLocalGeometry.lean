/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardFlatSpinor
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

theorem surfaceIntersection_add_left {g : Nat}
    (h k l : SurfaceHomology g) :
    surfaceIntersection (h + k) l =
      surfaceIntersection h l + surfaceIntersection k l := by
  unfold surfaceIntersection
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [add_mul]
  abel

theorem surfaceIntersection_finset_sum_left {g : Nat}
    {I : Type*} [DecidableEq I] (S : Finset I)
    (f : I -> SurfaceHomology g) (h : SurfaceHomology g) :
    surfaceIntersection (∑ i ∈ S, f i) h =
      ∑ i ∈ S, surfaceIntersection (f i) h := by
  induction S using Finset.induction_on with
  | empty => simp [surfaceIntersection]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        surfaceIntersection_add_left, ih]


theorem surfaceIntersection_subgraphHomology_eq_doubleSum
    {g : Nat} {V : Type*} [DecidableEq V]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (F K : Finset (Sym2 V)) :
    surfaceIntersection
        (surfaceSubgraphHomology edgeClass F)
        (surfaceSubgraphHomology edgeClass K) =
      ∑ edge ∈ F, ∑ other ∈ K,
        surfaceIntersection (edgeClass edge) (edgeClass other) := by
  unfold surfaceSubgraphHomology
  rw [surfaceIntersection_finset_sum_left]
  apply Finset.sum_congr rfl
  intro edge _
  rw [surfaceIntersection_finset_sum_right]


end StatMech.FrontierA
