/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricAtlas.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


namespace ClosedMetricFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


noncomputable def phase (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    (dart next : G.Dart) : Complex :=
  kwAngleTurnPhase (atlas.angle dart) (atlas.angle next)


noncomputable def direction
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    (dart : G.Dart) : Complex :=
  atlas.angle dart |>.toCircle

end ClosedMetricFlatSurfaceGraphAtlas
end StatMech.FrontierA
