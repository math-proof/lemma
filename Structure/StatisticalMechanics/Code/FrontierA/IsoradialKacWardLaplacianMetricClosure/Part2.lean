/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacianMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardMetricClosure.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacianAtlas
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacianMetricClosure
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


structure MetricCriticalIsoradialGenusZeroOneEmbedding
    (g : Nat) {GraphVertex : Type u}
    [Fintype GraphVertex] [DecidableEq GraphVertex]
    (G : SimpleGraph GraphVertex) [DecidableRel G.Adj]
    (DualVertex Qprimal Qdual Component : Type u)
    [Fintype DualVertex] [DecidableEq DualVertex]
    [Fintype Qprimal] [DecidableEq Qprimal]
    [Fintype Qdual] [DecidableEq Qdual]
    [Fintype Component] [DecidableEq Component] where
  isoradial : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
    g G DualVertex Qprimal Qdual
  genus_le_one : g ≤ 1
  thetaVertex : GraphVertex -> GraphVertex -> Real
  transport : GraphVertex -> GraphVertex -> Complex
  componentOrientation : IsoradialMetricComponentOrientationData Component
    isoradial.polygonalAtlas.cellular.ribbonSystem isoradial.character
    (fun edge => isoradialCriticalMu (isoradial.theta edge))
    (isoradialMuConductance thetaVertex) transport

end StatMech.FrontierA
