/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardMetricClosure
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

variable {E D Q : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]


structure MetricCriticalIsoradialClosedFlatSurfaceEmbedding
    (g : Nat) {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (DualVertex Qprimal Qdual : Type u)
    [Fintype DualVertex] [DecidableEq DualVertex]
    [Fintype Qprimal] [DecidableEq Qprimal]
    [Fintype Qdual] [DecidableEq Qdual] where
  polygonalAtlas :
    ClosedPolygonalFlatSurfaceGraphAtlas g (Sum V DualVertex) G
  dualVertexCount_eq :
    polygonalAtlas.cellular.faceCount = Fintype.card DualVertex
  theta : finiteGraphEdge G -> Real
  theta_pos : forall edge, 0 < theta edge
  theta_lt : forall edge, theta edge < Real.pi / 2
  primalConeIndex : V -> Nat
  dualConeIndex : DualVertex -> Nat
  primalRhombusIncidence : V -> finiteGraphEdge G -> Nat
  dualRhombusIncidence : DualVertex -> finiteGraphEdge G -> Nat
  primalRhombusIncidence_total : forall edge,
    ∑ vertex : V, primalRhombusIncidence vertex edge = 2
  dualRhombusIncidence_total : forall edge,
    ∑ vertex : DualVertex, dualRhombusIncidence vertex edge = 2
  primalConeAngle : forall vertex,
    (∑ edge : finiteGraphEdge G,
      (primalRhombusIncidence vertex edge : Real) * theta edge) =
        Real.pi * (2 * (primalConeIndex vertex : Real) + 1)
  dualConeAngle : forall vertex,
    (∑ edge : finiteGraphEdge G,
      (dualRhombusIncidence vertex edge : Real) *
        (Real.pi / 2 - theta edge)) =
      Real.pi * (2 * (dualConeIndex vertex : Real) + 1)
  boundaryAngle : forall F : Finset (finiteGraphEdge G),
    Fin (polygonalAtlas.cellular.ribbonSystem.boundaryComponents F) -> Real
  boundaryAngle_sum_zero : forall F : Finset (finiteGraphEdge G),
    ∑ boundary, boundaryAngle F boundary = 0
  primalKacWard : Matrix Qprimal Qprimal Complex
  dualKacWard : Matrix Qdual Qdual Complex
  primalPermutationExpansion : IsoradialMetricPermutationExpansion
    polygonalAtlas.cellular.ribbonSystem
    (fun F boundary => Complex.exp
      ((boundaryAngle F boundary : Complex) * Complex.I))
    primalKacWard theta
    (fun vertex => decide (primalConeIndex vertex % 2 = 1))
  dualPermutationExpansion : IsoradialMetricPermutationExpansion
    polygonalAtlas.cellular.ribbonSystem.dualRibbonSystem
    (polygonalAtlas.cellular.ribbonSystem.dualBoundaryCharacter
      (fun F boundary => Complex.exp
        ((boundaryAngle F boundary : Complex) * Complex.I)))
    dualKacWard (fun edge => Real.pi / 2 - theta edge)
    (fun vertex => decide (dualConeIndex vertex % 2 = 1))

end StatMech.FrontierA
