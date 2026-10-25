/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part3


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

theorem CriticalIsoradialDualityCertificate.normalized_det_eq
    {PrimalVertex DualVertex Dart Q Qstar : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (theta : E -> Real)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (certificate : CriticalIsoradialDualityCertificate
      PrimalVertex DualVertex Dart Q Qstar R C
      character theta primalExceptional dualExceptional
      primalKacWard dualKacWard) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization PrimalVertex theta *
        (1 - primalKacWard).det :=
  normalized_isoradialKacWard_duality_of_canonicalDualRibbon
    R C character certificate.character_ne certificate.character_total
    theta certificate.theta_pos certificate.theta_lt
    primalExceptional dualExceptional
    primalKacWard dualKacWard certificate.primalCoefficient
    certificate.dualCoefficient
    certificate.oddConeGaussBonnet

namespace FiniteCellularGraphEmbedding


theorem normalized_isoradialKacWard_duality
    {V DualVertex Q Qstar : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (embedding : FiniteCellularGraphEmbedding G)
    (dualVertexCount_eq : embedding.faceCount = Fintype.card DualVertex)
    (character : forall F : Finset (finiteGraphEdge G),
      Fin (embedding.ribbonSystem.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset (finiteGraphEdge G))
      (boundary : Fin (embedding.ribbonSystem.boundaryComponents F)),
        character F boundary ≠ 0)
    (htotal : forall F : Finset (finiteGraphEdge G),
      ∏ boundary, character F boundary = 1)
    (theta : finiteGraphEdge G -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2)
    (primalExceptional : V -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalConeIndex : V -> Nat)
    (dualConeIndex : DualVertex -> Nat)
    (primalExceptional_iff : forall vertex,
      primalExceptional vertex = true ↔ primalConeIndex vertex % 2 = 1)
    (dualExceptional_iff : forall vertex,
      dualExceptional vertex = true ↔ dualConeIndex vertex % 2 = 1)
    (coneIndexGaussBonnet :
      (∑ vertex : V, primalConeIndex vertex) +
        (∑ vertex : DualVertex, dualConeIndex vertex) + 1 =
          embedding.genus)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (primalExpansion : CriticalKacWardRibbonCoefficientIdentification
      embedding.ribbonSystem character primalKacWard theta
      primalExceptional)
    (dualExpansion : CriticalKacWardRibbonCoefficientIdentification
      embedding.ribbonSystem.dualRibbonSystem
      (embedding.ribbonSystem.dualBoundaryCharacter character) dualKacWard
      (fun edge => Real.pi / 2 - theta edge)
      dualExceptional) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization V theta *
        (1 - primalKacWard).det := by
  let oddConeGaussBonnet : IsoradialOddConeGaussBonnetData
      V DualVertex embedding.ribbonSystem embedding.cellularDualData
      primalExceptional dualExceptional :=
    { primalVertexCount_eq := rfl
      dualVertexCount_eq := dualVertexCount_eq
      primalConeIndex := primalConeIndex
      dualConeIndex := dualConeIndex
      primalExceptional_iff := primalExceptional_iff
      dualExceptional_iff := dualExceptional_iff
      coneIndexGaussBonnet := coneIndexGaussBonnet }
  exact normalized_isoradialKacWard_duality_of_canonicalDualRibbon
    embedding.ribbonSystem embedding.cellularDualData character
    hcharacter htotal theta htheta htheta' primalExceptional dualExceptional
    primalKacWard dualKacWard primalExpansion dualExpansion
    oddConeGaussBonnet

end FiniteCellularGraphEmbedding
end StatMech.FrontierA
