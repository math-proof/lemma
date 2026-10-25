/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialKacWardMetricClosure.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

variable {E D Q : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]


namespace MetricCriticalIsoradialClosedFlatSurfaceEmbedding

variable {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {DualVertex Qprimal Qdual : Type u}
  [Fintype DualVertex] [DecidableEq DualVertex]
  [Fintype Qprimal] [DecidableEq Qprimal]
  [Fintype Qdual] [DecidableEq Qdual]


noncomputable def character
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual)
    (F : Finset (finiteGraphEdge G))
    (boundary : Fin
      (embedding.polygonalAtlas.cellular.ribbonSystem.boundaryComponents F)) :
    Complex :=
  Complex.exp ((embedding.boundaryAngle F boundary : Complex) * Complex.I)

end MetricCriticalIsoradialClosedFlatSurfaceEmbedding
end StatMech.FrontierA
