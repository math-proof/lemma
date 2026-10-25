/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part7
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u


namespace CriticalIsoradialClosedFlatSurfaceEmbedding

noncomputable def toAdmissibleClosedFlatSurfaceEmbedding
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    (embedding : CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Q Qstar) :
    AdmissibleClosedFlatSurfaceEmbedding g G :=
  embedding.atlas.toAdmissibleEmbedding embedding.admissibleConeAngles


noncomputable def toOddConeGaussBonnetData
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    (embedding : CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Q Qstar) :
    IsoradialOddConeGaussBonnetData V DualVertex
      embedding.atlas.cellular.ribbonSystem
      embedding.atlas.cellular.cellularDualData
      embedding.primalExceptional embedding.dualExceptional where
  primalVertexCount_eq := rfl
  dualVertexCount_eq := embedding.dualVertexCount_eq
  primalConeIndex := embedding.primalConeIndex
  dualConeIndex := embedding.dualConeIndex
  primalExceptional_iff := embedding.primalExceptional_iff
  dualExceptional_iff := embedding.dualExceptional_iff
  coneIndexGaussBonnet := embedding.coneIndexGaussBonnet


noncomputable def toDualityCertificate
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    (embedding : CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Q Qstar) :
    CriticalIsoradialDualityCertificate
      V DualVertex G.Dart Q Qstar
      embedding.atlas.cellular.ribbonSystem
      embedding.atlas.cellular.cellularDualData
      embedding.character embedding.theta
      embedding.primalExceptional embedding.dualExceptional
      embedding.primalKacWard embedding.dualKacWard where
  theta_pos := embedding.theta_pos
  theta_lt := embedding.theta_lt
  character_ne := embedding.character_ne
  character_total := embedding.character_total
  primalCoefficient := embedding.primalCoefficient
  dualCoefficient := embedding.dualCoefficient
  oddConeGaussBonnet := embedding.toOddConeGaussBonnetData


end CriticalIsoradialClosedFlatSurfaceEmbedding
end StatMech.FrontierA
