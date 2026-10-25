/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricAtlas
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


theorem kwClosedWalkAngleRotationNumber_spec
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (angle : G.Dart -> Real.Angle) {root : V}
    (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, (angle (kwGraphCycleDartLoop p (k + 1)) -
        angle (kwGraphCycleDartLoop p k)).toReal : Real) =
      (kwClosedWalkAngleRotationNumber angle p : Real) *
        (2 * Real.pi) := by
  let hne : p.darts.length ≠ 0 :=
    Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))
  letI : NeZero p.darts.length := ⟨hne⟩
  rw [kwClosedWalkAngleRotationNumber, dif_neg hne]
  exact Classical.choose_spec
    (kw_totalPrincipalTurn_eq_int_mul_two_pi angle
      (kwGraphCycleDartLoop p))


end StatMech.FrontierA
