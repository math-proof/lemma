/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part2


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

namespace IsoradialOddConeGaussBonnetData

omit [DecidableEq E] in


theorem toGaussBonnetParity
    {PrimalVertex DualVertex Dart : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (data : IsoradialOddConeGaussBonnetData
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    IsoradialDualGaussBonnetParity
      PrimalVertex DualVertex R C primalExceptional dualExceptional := by
  refine
    { primalVertexCount_eq := data.primalVertexCount_eq
      dualVertexCount_eq := data.dualVertexCount_eq
      exceptionParity := ?_ }
  have hprimal := coneExceptionCount_mod_two_eq_sum
    PrimalVertex primalExceptional data.primalConeIndex
      data.primalExceptional_iff
  have hdual := coneExceptionCount_mod_two_eq_sum
    DualVertex dualExceptional data.dualConeIndex data.dualExceptional_iff
  have hgaussBonnet := data.coneIndexGaussBonnet
  omega

end IsoradialOddConeGaussBonnetData

namespace IsoradialDualGaussBonnetParity

omit [DecidableEq E] in


theorem conePhaseBalance
    {PrimalVertex DualVertex Dart : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (gaussBonnet : IsoradialDualGaussBonnetParity
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    IsoradialDualConePhaseBalance
      PrimalVertex DualVertex R C primalExceptional dualExceptional := by
  classical
  refine
    { dualVertexCount_eq := gaussBonnet.dualVertexCount_eq
      phaseBalance := ?_ }
  rw [prod_coneQuarterPhase DualVertex dualExceptional,
    prod_coneQuarterPhase PrimalVertex primalExceptional]
  have heuler := C.cellularEuler
  rw [gaussBonnet.primalVertexCount_eq,
    gaussBonnet.dualVertexCount_eq] at heuler
  have hparity := gaussBonnet.exceptionParity
  have hmod :
      (Fintype.card DualVertex +
          2 * coneExceptionCount dualExceptional +
          3 * Fintype.card E) % 4 =
        (2 * Fintype.card PrimalVertex +
          (Fintype.card PrimalVertex +
            2 * coneExceptionCount primalExceptional)) % 4 := by
    omega
  have hneg : (-1 : Complex) = Complex.I ^ 2 := by
    norm_num [Complex.I_mul_I]
  have hnegI : -Complex.I = Complex.I ^ 3 := by
    norm_num [Complex.I_mul_I]
  rw [hneg, hnegI]
  simp only [← pow_mul, ← pow_add]
  exact pow_eq_pow_of_modEq hmod (by norm_num [Complex.I_mul_I])

end IsoradialDualGaussBonnetParity


theorem normalized_isoradialKacWard_duality
    {PrimalVertex DualVertex Dart Q Qstar : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset E)
      (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
    (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
    (theta : E -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (primalExpansion : KacWardSubgraphCoefficientIdentification
      (ribbonBoundaryCharacterCoefficient R character) primalKacWard
      (fun edge => isoradialCriticalMu (theta edge))
      (criticalKacWardRibbonPrefactor theta primalExceptional))
    (dualExpansion : KacWardSubgraphCoefficientIdentification
      (dualRibbonBoundaryCharacterCoefficient R character) dualKacWard
      (fun edge => isoradialCriticalMu (Real.pi / 2 - theta edge))
      (criticalKacWardRibbonPrefactor
        (fun edge => Real.pi / 2 - theta edge) dualExceptional))
    (cone : IsoradialDualConePhaseBalance
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization PrimalVertex theta *
        (1 - primalKacWard).det := by
  have hdualPos (edge : E) : 0 < Real.pi / 2 - theta edge := by
    linarith [htheta' edge]
  have hdualLt (edge : E) :
      Real.pi / 2 - theta edge < Real.pi / 2 := by
    linarith [htheta edge]
  rw [dualExpansion.expansion, primalExpansion.expansion]
  rw [cellularRibbon_isoradialCritical_subgraphSum_duality
    R C character hcharacter htotal theta htheta htheta']
  rw [← mul_assoc
      (kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge))
      (criticalKacWardRibbonPrefactor
        (fun edge => Real.pi / 2 - theta edge) dualExceptional)]
  rw [← mul_assoc
      (kwIsoradialDualityNormalization PrimalVertex theta)
      (criticalKacWardRibbonPrefactor theta primalExceptional)]
  rw [kwIsoradialDualityNormalization_mul_prefactor
      (fun edge => Real.pi / 2 - theta edge) dualExceptional
      hdualPos hdualLt,
    kwIsoradialDualityNormalization_mul_prefactor
      theta primalExceptional htheta htheta']
  rw [cone.dualVertexCount_eq]
  have hedgeProduct := prod_isoradial_dualCos_mul_criticalMu_inv
    theta htheta htheta'
  have hsign :
      (-1 : Complex) ^ Fintype.card DualVertex *
          (-1 : Complex) ^ Fintype.card DualVertex = 1 := by
    rw [← mul_pow]
    norm_num
  let signDual : Complex := (-1 : Complex) ^ Fintype.card DualVertex
  let signPrimal : Complex := (-1 : Complex) ^ Fintype.card PrimalVertex
  let twoEdges : Complex := (2 : Complex) ^ Fintype.card E
  let phaseDual : Complex :=
    ∏ vertex : DualVertex, coneQuarterPhase dualExceptional vertex
  let phasePrimal : Complex :=
    ∏ vertex : PrimalVertex, coneQuarterPhase primalExceptional vertex
  let cosDual : Complex :=
    ∏ edge : E, (Real.cos (Real.pi / 2 - theta edge) : Complex)
  let cosPrimal : Complex :=
    ∏ edge : E, (Real.cos (theta edge) : Complex)
  let muInv : Complex :=
    (∏ edge : E, isoradialCriticalMu (theta edge))⁻¹
  let subgraphSum : Complex :=
    kwDualSubgraphSum
      (ribbonBoundaryCharacterCoefficient R character)
      (fun edge => isoradialCriticalMu (theta edge))
  change ((signDual * twoEdges * phaseDual) * cosDual) *
      (signDual * (muInv * subgraphSum)) =
    ((signPrimal * twoEdges * phasePrimal) * cosPrimal) * subgraphSum
  have hsign' : signDual * signDual = 1 := hsign
  have hedgeProduct' :
      cosDual * muInv = (-Complex.I) ^ Fintype.card E * cosPrimal :=
    hedgeProduct
  have hphase :
      phaseDual * (-Complex.I) ^ Fintype.card E =
        signPrimal * phasePrimal := cone.phaseBalance
  calc
    ((signDual * twoEdges * phaseDual) * cosDual) *
        (signDual * (muInv * subgraphSum)) =
      (signDual * signDual) * twoEdges * phaseDual *
        (cosDual * muInv) * subgraphSum := by ring
    _ = twoEdges *
        (phaseDual * (-Complex.I) ^ Fintype.card E) *
        cosPrimal * subgraphSum := by
      rw [hsign', one_mul, hedgeProduct']
      ring
    _ = ((signPrimal * twoEdges * phasePrimal) * cosPrimal) *
        subgraphSum := by
      rw [hphase]
      ring


theorem normalized_isoradialKacWard_duality_of_gaussBonnet
    {PrimalVertex DualVertex Dart Q Qstar : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset E)
      (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
    (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
    (theta : E -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (primalExpansion : KacWardSubgraphCoefficientIdentification
      (ribbonBoundaryCharacterCoefficient R character) primalKacWard
      (fun edge => isoradialCriticalMu (theta edge))
      (criticalKacWardRibbonPrefactor theta primalExceptional))
    (dualExpansion : KacWardSubgraphCoefficientIdentification
      (dualRibbonBoundaryCharacterCoefficient R character) dualKacWard
      (fun edge => isoradialCriticalMu (Real.pi / 2 - theta edge))
      (criticalKacWardRibbonPrefactor
        (fun edge => Real.pi / 2 - theta edge) dualExceptional))
    (gaussBonnet : IsoradialDualGaussBonnetParity
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization PrimalVertex theta *
        (1 - primalKacWard).det :=
  normalized_isoradialKacWard_duality R C character hcharacter htotal
    theta htheta htheta' primalExceptional dualExceptional
    primalKacWard dualKacWard primalExpansion dualExpansion
    (gaussBonnet.conePhaseBalance R C
      primalExceptional dualExceptional)


theorem normalized_isoradialKacWard_duality_of_ribbonCoefficients
    {PrimalVertex DualVertex Dart DualDart Q Qstar : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype DualDart] [DecidableEq DualDart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (Rdual : RibbonPermutationSystem E DualDart)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (dualCharacter : forall F : Finset E,
      Fin (Rdual.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset E)
      (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
    (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
    (boundaryIdentification : RibbonDualBoundaryIdentification R Rdual)
    (dualCharacter_reverse : forall (F : Finset E)
      (boundary : Fin (Rdual.boundaryComponents F)),
      dualCharacter F boundary =
        (character Fᶜ
          (boundaryIdentification.boundaryEquiv F boundary))⁻¹)
    (theta : E -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (primalCoefficient : CriticalKacWardRibbonCoefficientIdentification
      R character primalKacWard theta primalExceptional)
    (dualCoefficient : CriticalKacWardRibbonCoefficientIdentification
      Rdual dualCharacter dualKacWard
      (fun edge => Real.pi / 2 - theta edge) dualExceptional)
    (gaussBonnet : IsoradialDualGaussBonnetParity
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization PrimalVertex theta *
        (1 - primalKacWard).det :=
  normalized_isoradialKacWard_duality_of_gaussBonnet
    R C character hcharacter htotal theta htheta htheta'
    primalExceptional dualExceptional primalKacWard dualKacWard
    (primalCoefficient.toSubgraphCoefficientIdentification
      R character primalKacWard theta primalExceptional)
    (dualCoefficient.toDualSubgraphCoefficientIdentification
      Rdual dualCharacter dualKacWard
      (fun edge => Real.pi / 2 - theta edge) dualExceptional
      R character (ribbonBoundaryCharacterCoefficient_dual
        R Rdual boundaryIdentification character dualCharacter
        dualCharacter_reverse))
    gaussBonnet


theorem normalized_isoradialKacWard_duality_of_canonicalDualRibbon
    {PrimalVertex DualVertex Dart Q Qstar : Type*}
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (hcharacter : forall (F : Finset E)
      (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
    (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
    (theta : E -> Real)
    (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex)
    (primalCoefficient : CriticalKacWardRibbonCoefficientIdentification
      R character primalKacWard theta primalExceptional)
    (dualCoefficient : CriticalKacWardRibbonCoefficientIdentification
      R.dualRibbonSystem (R.dualBoundaryCharacter character) dualKacWard
      (fun edge => Real.pi / 2 - theta edge) dualExceptional)
    (oddConeGaussBonnet : IsoradialOddConeGaussBonnetData
      PrimalVertex DualVertex R C primalExceptional dualExceptional) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - theta edge) *
        (1 - dualKacWard).det =
      kwIsoradialDualityNormalization PrimalVertex theta *
        (1 - primalKacWard).det :=
  normalized_isoradialKacWard_duality_of_ribbonCoefficients
    R C R.dualRibbonSystem character (R.dualBoundaryCharacter character)
    hcharacter htotal R.dualBoundaryIdentification
    (R.dualBoundaryCharacter_reverse character) theta htheta htheta'
    primalExceptional dualExceptional primalKacWard dualKacWard
    primalCoefficient dualCoefficient
    (oddConeGaussBonnet.toGaussBonnetParity
      R C primalExceptional dualExceptional)


end StatMech.FrontierA
