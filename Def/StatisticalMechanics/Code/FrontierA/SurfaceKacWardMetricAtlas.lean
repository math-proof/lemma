/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricAtlas
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


noncomputable def kwClosedWalkAngleRotationNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (angle : G.Dart -> Real.Angle) {root : V}
    (p : G.Walk root root) : Int :=
  if h : p.darts.length = 0 then 0 else by
    letI : NeZero p.darts.length := ⟨h⟩
    exact Classical.choose
      (kw_totalPrincipalTurn_eq_int_mul_two_pi angle
        (kwGraphCycleDartLoop p))


end StatMech.FrontierA
