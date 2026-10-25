/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacianAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
open SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u


structure CriticalIsoradialGenusZeroOneEmbedding
    (g : Nat) {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (DualVertex Q Qstar Component : Type u)
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    [Fintype Component] [DecidableEq Component] where
  isoradial : CriticalIsoradialClosedFlatSurfaceEmbedding
    g G DualVertex Q Qstar
  thetaVertex : V -> V -> Real
  transport : V -> V -> Complex
  componentIdentification : GenusZeroOneRibbonComponentIdentification
    Component isoradial.atlas.cellular.ribbonSystem
    isoradial.atlas.cellular.cellularDualData isoradial.character
    (fun edge => isoradialCriticalMu (isoradial.theta edge))
    (isoradialMuConductance thetaVertex) transport

end StatMech.FrontierA
