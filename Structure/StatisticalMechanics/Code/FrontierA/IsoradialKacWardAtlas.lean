/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part7
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u


structure CriticalIsoradialClosedFlatSurfaceEmbedding
    (g : Nat) {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (DualVertex Q Qstar : Type u)
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar] where
  atlas : ClosedFlatSurfaceGraphAtlas g G
  admissibleConeAngles : atlas.AdmissibleConeAngles
  dualVertexCount_eq : atlas.cellular.faceCount = Fintype.card DualVertex
  theta : finiteGraphEdge G -> Real
  theta_pos : forall edge, 0 < theta edge
  theta_lt : forall edge, theta edge < Real.pi / 2
  primalExceptional : V -> Bool
  dualExceptional : DualVertex -> Bool
  primalConeIndex : V -> Nat
  dualConeIndex : DualVertex -> Nat
  primalExceptional_iff : forall vertex,
    primalExceptional vertex = true ↔ primalConeIndex vertex % 2 = 1
  dualExceptional_iff : forall vertex,
    dualExceptional vertex = true ↔ dualConeIndex vertex % 2 = 1
  coneIndexGaussBonnet :
    (∑ vertex : V, primalConeIndex vertex) +
      (∑ vertex : DualVertex, dualConeIndex vertex) + 1 =
        atlas.cellular.genus
  character : forall F : Finset (finiteGraphEdge G),
    Fin (atlas.cellular.ribbonSystem.boundaryComponents F) -> Complex
  character_ne : forall (F : Finset (finiteGraphEdge G))
    (boundary : Fin (atlas.cellular.ribbonSystem.boundaryComponents F)),
      character F boundary ≠ 0
  character_total : forall F : Finset (finiteGraphEdge G),
    ∏ boundary, character F boundary = 1
  primalKacWard : Matrix Q Q Complex
  dualKacWard : Matrix Qstar Qstar Complex
  primalCoefficient : CriticalKacWardRibbonCoefficientIdentification
    atlas.cellular.ribbonSystem character primalKacWard theta
      primalExceptional
  dualCoefficient : CriticalKacWardRibbonCoefficientIdentification
    atlas.cellular.ribbonSystem.dualRibbonSystem
    (atlas.cellular.ribbonSystem.dualBoundaryCharacter character)
    dualKacWard (fun edge => Real.pi / 2 - theta edge) dualExceptional

end StatMech.FrontierA
