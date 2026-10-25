/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardMetricClosure.Part2
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


noncomputable def toCriticalIsoradialClosedFlatSurfaceEmbedding
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) :
    CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual where
  atlas := embedding.polygonalAtlas.toClosedMetricFlatSurfaceGraphAtlas
    |>.toClosedFlatSurfaceGraphAtlas
  admissibleConeAngles :=
    embedding.polygonalAtlas.toClosedMetricFlatSurfaceGraphAtlas
      |>.toClosedFlatSurfaceGraphAtlas_admissible
  dualVertexCount_eq := embedding.dualVertexCount_eq
  theta := embedding.theta
  theta_pos := embedding.theta_pos
  theta_lt := embedding.theta_lt
  primalExceptional := embedding.primalExceptional
  dualExceptional := embedding.dualExceptional
  primalConeIndex := embedding.primalConeIndex
  dualConeIndex := embedding.dualConeIndex
  primalExceptional_iff := embedding.primalExceptional_iff
  dualExceptional_iff := embedding.dualExceptional_iff
  coneIndexGaussBonnet := by
    change (∑ vertex : V, embedding.primalConeIndex vertex) +
      (∑ vertex : DualVertex, embedding.dualConeIndex vertex) + 1 =
        embedding.polygonalAtlas.cellular.genus
    rw [embedding.polygonalAtlas.genus_eq]
    exact embedding.coneIndexGaussBonnet
  character := embedding.character
  character_ne := embedding.character_ne
  character_total := embedding.character_total
  primalKacWard := embedding.primalKacWard
  dualKacWard := embedding.dualKacWard
  primalCoefficient :=
    embedding.primalPermutationExpansion.toCoefficientIdentification
      embedding.polygonalAtlas.cellular.ribbonSystem embedding.character
      embedding.primalKacWard embedding.theta embedding.primalExceptional
  dualCoefficient :=
    embedding.dualPermutationExpansion.toCoefficientIdentification
      embedding.polygonalAtlas.cellular.ribbonSystem.dualRibbonSystem
      (embedding.polygonalAtlas.cellular.ribbonSystem.dualBoundaryCharacter
        embedding.character)
      embedding.dualKacWard (fun edge => Real.pi / 2 - embedding.theta edge)
      embedding.dualExceptional


end MetricCriticalIsoradialClosedFlatSurfaceEmbedding
end StatMech.FrontierA
