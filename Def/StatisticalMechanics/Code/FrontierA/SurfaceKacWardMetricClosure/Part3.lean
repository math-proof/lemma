/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricAtlas.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardMetricClosure.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v

namespace ClosedMetricFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


noncomputable def toAdmissibleEmbedding
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G) :
    AdmissibleClosedFlatSurfaceEmbedding g G :=
  atlas.toClosedFlatSurfaceGraphAtlas.toAdmissibleEmbedding
    atlas.toClosedFlatSurfaceGraphAtlas_admissible


end ClosedMetricFlatSurfaceGraphAtlas
end StatMech.FrontierA
