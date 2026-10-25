/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacianMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardMetricClosure.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacianAtlas
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacianMetricClosure.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

variable {V E D Component : Type*}
  [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  [Fintype Component] [DecidableEq Component]


namespace MetricCriticalIsoradialGenusZeroOneEmbedding

variable {g : Nat} {GraphVertex : Type u}
  [Fintype GraphVertex] [DecidableEq GraphVertex]
  {G : SimpleGraph GraphVertex} [DecidableRel G.Adj]
  {DualVertex Qprimal Qdual Component : Type u}
  [Fintype DualVertex] [DecidableEq DualVertex]
  [Fintype Qprimal] [DecidableEq Qprimal]
  [Fintype Qdual] [DecidableEq Qdual]
  [Fintype Component] [DecidableEq Component]


noncomputable def toCriticalIsoradialGenusZeroOneEmbedding
    (embedding : MetricCriticalIsoradialGenusZeroOneEmbedding
      g G DualVertex Qprimal Qdual Component) :
    CriticalIsoradialGenusZeroOneEmbedding
      g G DualVertex Qprimal Qdual Component where
  isoradial :=
    embedding.isoradial.toCriticalIsoradialClosedFlatSurfaceEmbedding
  thetaVertex := embedding.thetaVertex
  transport := embedding.transport
  componentIdentification :=
    embedding.componentOrientation.toComponentIdentification
      embedding.isoradial.polygonalAtlas.cellular.ribbonSystem
      embedding.isoradial.polygonalAtlas.cellular.cellularDualData
      embedding.isoradial.character
      (fun edge => isoradialCriticalMu (embedding.isoradial.theta edge))
      (isoradialMuConductance embedding.thetaVertex) embedding.transport
      (by
        change embedding.isoradial.polygonalAtlas.cellular.genus ≤ 1
        rw [embedding.isoradial.polygonalAtlas.genus_eq]
        exact embedding.genus_le_one)


end MetricCriticalIsoradialGenusZeroOneEmbedding
end StatMech.FrontierA
