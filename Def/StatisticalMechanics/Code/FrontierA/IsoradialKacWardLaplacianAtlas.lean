/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacianAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacianAtlas
open SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u


namespace CriticalIsoradialGenusZeroOneEmbedding

noncomputable def toRibbonCertificate
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar Component : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    [Fintype Component] [DecidableEq Component]
    (embedding : CriticalIsoradialGenusZeroOneEmbedding
      g G DualVertex Q Qstar Component) :
    CriticalIsoradialEmbeddingRibbonCertificate Component
      embedding.isoradial.atlas.cellular.ribbonSystem
      embedding.isoradial.atlas.cellular.cellularDualData
      embedding.isoradial.character embedding.isoradial.primalKacWard
      embedding.thetaVertex embedding.isoradial.theta embedding.transport
      embedding.isoradial.primalExceptional where
  componentIdentification := embedding.componentIdentification
  coefficientIdentification := embedding.isoradial.primalCoefficient


end CriticalIsoradialGenusZeroOneEmbedding
end StatMech.FrontierA
