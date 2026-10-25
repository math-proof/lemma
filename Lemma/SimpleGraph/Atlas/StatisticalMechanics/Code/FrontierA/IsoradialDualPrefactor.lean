import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part7
open StatMech StatMech.FrontierA StatMech.FrontierA.RibbonPermutationSystem StatMech.FrontierA.KacWardSubgraphCoefficientIdentification StatMech.FrontierA.IsoradialOddConeGaussBonnetData StatMech.FrontierA.IsoradialDualGaussBonnetParity StatMech.FrontierA.FiniteCellularGraphEmbedding


/--
[isoradial_dualCos_mul_criticalMu_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma isoradial_dualCos_mul_criticalMu_inv_eq
  {theta : Real}
-- given
  (htheta : 0 < theta)
  (htheta' : theta < Real.pi / 2) :
-- imply
  (Real.cos (Real.pi / 2 - theta) : Complex) * (isoradialCriticalMu theta)⁻¹ = -Complex.I * (Real.cos theta : Complex) := by
-- proof
  apply StatMech.FrontierA.isoradial_dualCos_mul_criticalMu_inv theta htheta htheta'

/--
[prod_isoradial_dualCos_mul_criticalMu_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma prod_isoradial_dualCos_mul_criticalMu_inv_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (theta : E -> Real)
  (htheta : forall edge, 0 < theta edge)
  (htheta' : forall edge, theta edge < Real.pi / 2) :
-- imply
  (∏ edge : E, (Real.cos (Real.pi / 2 - theta edge) : Complex)) * (∏ edge : E, isoradialCriticalMu (theta edge))⁻¹ = (-Complex.I) ^ Fintype.card E * ∏ edge : E, (Real.cos (theta edge) : Complex) := by
-- proof
  apply StatMech.FrontierA.prod_isoradial_dualCos_mul_criticalMu_inv theta htheta htheta'

/--
[kwIsoradialDualityNormalization_mul_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma kwIsoradialDualityNormalization_mul_prefactor_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype Vertex]
-- given
  (theta : E -> Real)
  (exceptional : Vertex -> Bool)
  (htheta : forall edge, 0 < theta edge)
  (htheta' : forall edge, theta edge < Real.pi / 2) :
-- imply
  kwIsoradialDualityNormalization Vertex theta * criticalKacWardRibbonPrefactor theta exceptional = (-1 : Complex) ^ Fintype.card Vertex * (2 : Complex) ^ Fintype.card E * (∏ vertex : Vertex, coneQuarterPhase exceptional vertex) * ∏ edge : E, (Real.cos (theta edge) : Complex) := by
-- proof
  apply StatMech.FrontierA.kwIsoradialDualityNormalization_mul_prefactor theta exceptional htheta htheta'

/--
[prod_coneQuarterPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma prod_coneQuarterPhase_eq
  [Fintype E]
  [DecidableEq E]
  {Vertex : Type*}
  [Fintype Vertex]
-- given
  (exceptional : Vertex -> Bool) :
-- imply
  (∏ vertex : Vertex, coneQuarterPhase exceptional vertex) = Complex.I ^ Fintype.card Vertex * (-1 : Complex) ^ coneExceptionCount exceptional := by
-- proof
  apply StatMech.FrontierA.prod_coneQuarterPhase Vertex exceptional

/--
[coneExceptionCount_mod_two_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma coneExceptionCount_mod_two_eq_sum_eq
  [Fintype E]
  [DecidableEq E]
  {Vertex : Type*}
  [Fintype Vertex]
-- given
  (exceptional : Vertex -> Bool)
  (coneIndex : Vertex -> Nat)
  (hexceptional : forall vertex, exceptional vertex = true ↔ coneIndex vertex % 2 = 1) :
-- imply
  coneExceptionCount exceptional % 2 = (∑ vertex : Vertex, coneIndex vertex) % 2 := by
-- proof
  apply StatMech.FrontierA.coneExceptionCount_mod_two_eq_sum Vertex exceptional coneIndex hexceptional

/--
[edgeFlip_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma edgeFlip_mul_self_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {edge : E} :
-- imply
  R.edgeFlip edge * R.edgeFlip edge = 1 := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.edgeFlip_mul_self R edge

/--
[partialEdgeFlip_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma partialEdgeFlip_mul_self_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {F : Finset E} :
-- imply
  R.partialEdgeFlip F * R.partialEdgeFlip F = 1 := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.partialEdgeFlip_mul_self R F

/--
[partialEdgeFlip_univ_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma partialEdgeFlip_univ_mul_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {F : Finset E} :
-- imply
  R.partialEdgeFlip Finset.univ * R.partialEdgeFlip F = R.partialEdgeFlip Fᶜ := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.partialEdgeFlip_univ_mul R F

/--
[dualRibbonSystem_boundaryPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma dualRibbonSystem_boundaryPerm_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {F : Finset E} :
-- imply
  R.dualRibbonSystem.boundaryPerm F = R.boundaryPerm Fᶜ := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.dualRibbonSystem_boundaryPerm R F

/--
[dualRibbonSystem_boundaryComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma dualRibbonSystem_boundaryComponents_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {F : Finset E} :
-- imply
  R.dualRibbonSystem.boundaryComponents F = R.boundaryComponents Fᶜ := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.dualRibbonSystem_boundaryComponents R F

/--
[dualBoundaryCharacter_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma dualBoundaryCharacter_reverse_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {F : Finset E}
  {boundary : Fin (R.dualRibbonSystem.boundaryComponents F)}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex) :
-- imply
  R.dualBoundaryCharacter character F boundary = (character Fᶜ (R.dualBoundaryIdentification.boundaryEquiv F boundary))⁻¹ := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.dualBoundaryCharacter_reverse R character F boundary

/--
[ribbonBoundaryCharacterCoefficient_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma ribbonBoundaryCharacterCoefficient_dual_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype Dprimal]
  [DecidableEq Dprimal]
  [Fintype Ddual]
  [DecidableEq Ddual]
  {primalRibbon : RibbonPermutationSystem E Dprimal}
  {dualRibbon : RibbonPermutationSystem E Ddual}
  {identification : RibbonDualBoundaryIdentification primalRibbon dualRibbon}
  {F : Finset E}
-- given
  (primalCharacter : forall F : Finset E, Fin (primalRibbon.boundaryComponents F) -> Complex)
  (dualCharacter : forall F : Finset E, Fin (dualRibbon.boundaryComponents F) -> Complex)
  (character_reverse : forall (F : Finset E) (boundary : Fin (dualRibbon.boundaryComponents F)), dualCharacter F boundary = (primalCharacter Fᶜ (identification.boundaryEquiv F boundary))⁻¹) :
-- imply
  ribbonBoundaryCharacterCoefficient dualRibbon dualCharacter F = dualRibbonBoundaryCharacterCoefficient primalRibbon primalCharacter F := by
-- proof
  apply StatMech.FrontierA.ribbonBoundaryCharacterCoefficient_dual primalRibbon dualRibbon identification primalCharacter dualCharacter character_reverse F

/--
[dualBoundaryCharacterCoefficient_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma dualBoundaryCharacterCoefficient_eq_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {F : Finset E}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex) :
-- imply
  ribbonBoundaryCharacterCoefficient R.dualRibbonSystem (R.dualBoundaryCharacter character) F = dualRibbonBoundaryCharacterCoefficient R character F := by
-- proof
  apply StatMech.FrontierA.dualBoundaryCharacterCoefficient_eq R character F

/--
[expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma expansion_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype Q]
  [DecidableEq Q]
  {kacWard : Matrix Q Q Complex}
  {prefactor : Complex}
  {I : KacWardSubgraphCoefficientIdentification coefficient kacWard weight prefactor}
-- given
  (coefficient : Finset E -> Complex)
  (weight : E -> Complex) :
-- imply
  (1 - kacWard).det = prefactor * kwDualSubgraphSum coefficient weight := by
-- proof
  apply StatMech.FrontierA.KacWardSubgraphCoefficientIdentification.expansion coefficient kacWard weight prefactor I

/--
[toGaussBonnetParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma toGaussBonnetParity_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype PrimalVertex]
  [Fintype DualVertex]
  [Fintype Dart]
  [DecidableEq Dart]
  {R : RibbonPermutationSystem E Dart}
  {C : CellularRibbonDualData R}
  {data : IsoradialOddConeGaussBonnetData PrimalVertex DualVertex R C primalExceptional dualExceptional}
-- given
  (primalExceptional : PrimalVertex -> Bool)
  (dualExceptional : DualVertex -> Bool) :
-- imply
  IsoradialDualGaussBonnetParity PrimalVertex DualVertex R C primalExceptional dualExceptional := by
-- proof
  apply StatMech.FrontierA.IsoradialOddConeGaussBonnetData.toGaussBonnetParity R C primalExceptional dualExceptional data

/--
[conePhaseBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma conePhaseBalance_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype PrimalVertex]
  [Fintype DualVertex]
  [Fintype Dart]
  [DecidableEq Dart]
  {R : RibbonPermutationSystem E Dart}
  {C : CellularRibbonDualData R}
  {gaussBonnet : IsoradialDualGaussBonnetParity PrimalVertex DualVertex R C primalExceptional dualExceptional}
-- given
  (primalExceptional : PrimalVertex -> Bool)
  (dualExceptional : DualVertex -> Bool) :
-- imply
  IsoradialDualConePhaseBalance PrimalVertex DualVertex R C primalExceptional dualExceptional := by
-- proof
  apply StatMech.FrontierA.IsoradialDualGaussBonnetParity.conePhaseBalance R C primalExceptional dualExceptional gaussBonnet

/--
[normalized_isoradialKacWard_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma normalized_isoradialKacWard_duality_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype PrimalVertex]
  [Fintype DualVertex]
  [Fintype Dart]
  [DecidableEq Dart]
  [Fintype Q]
  [DecidableEq Q]
  [Fintype Qstar]
  [DecidableEq Qstar]
  {R : RibbonPermutationSystem E Dart}
  {C : CellularRibbonDualData R}
  {primalKacWard : Matrix Q Q Complex}
  {dualKacWard : Matrix Qstar Qstar Complex}
  {cone : IsoradialDualConePhaseBalance PrimalVertex DualVertex R C primalExceptional dualExceptional}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (hcharacter : forall (F : Finset E) (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
  (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
  (theta : E -> Real)
  (htheta : forall edge, 0 < theta edge)
  (htheta' : forall edge, theta edge < Real.pi / 2)
  (primalExceptional : PrimalVertex -> Bool)
  (dualExceptional : DualVertex -> Bool)
  (primalExpansion : KacWardSubgraphCoefficientIdentification (ribbonBoundaryCharacterCoefficient R character) primalKacWard (fun edge => isoradialCriticalMu (theta edge)) (criticalKacWardRibbonPrefactor theta primalExceptional))
  (dualExpansion : KacWardSubgraphCoefficientIdentification (dualRibbonBoundaryCharacterCoefficient R character) dualKacWard (fun edge => isoradialCriticalMu (Real.pi / 2 - theta edge)) (criticalKacWardRibbonPrefactor (fun edge => Real.pi / 2 - theta edge) dualExceptional)) :
-- imply
  kwIsoradialDualityNormalization DualVertex (fun edge => Real.pi / 2 - theta edge) * (1 - dualKacWard).det = kwIsoradialDualityNormalization PrimalVertex theta * (1 - primalKacWard).det := by
-- proof
  apply StatMech.FrontierA.normalized_isoradialKacWard_duality R C character hcharacter htotal theta htheta htheta' primalExceptional dualExceptional primalKacWard dualKacWard primalExpansion dualExpansion cone

/--
[normalized_isoradialKacWard_duality_of_gaussBonnet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma normalized_isoradialKacWard_duality_of_gaussBonnet_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype PrimalVertex]
  [Fintype DualVertex]
  [Fintype Dart]
  [DecidableEq Dart]
  [Fintype Q]
  [DecidableEq Q]
  [Fintype Qstar]
  [DecidableEq Qstar]
  {R : RibbonPermutationSystem E Dart}
  {C : CellularRibbonDualData R}
  {primalKacWard : Matrix Q Q Complex}
  {dualKacWard : Matrix Qstar Qstar Complex}
  {gaussBonnet : IsoradialDualGaussBonnetParity PrimalVertex DualVertex R C primalExceptional dualExceptional}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (hcharacter : forall (F : Finset E) (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
  (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
  (theta : E -> Real)
  (htheta : forall edge, 0 < theta edge)
  (htheta' : forall edge, theta edge < Real.pi / 2)
  (primalExceptional : PrimalVertex -> Bool)
  (dualExceptional : DualVertex -> Bool)
  (primalExpansion : KacWardSubgraphCoefficientIdentification (ribbonBoundaryCharacterCoefficient R character) primalKacWard (fun edge => isoradialCriticalMu (theta edge)) (criticalKacWardRibbonPrefactor theta primalExceptional))
  (dualExpansion : KacWardSubgraphCoefficientIdentification (dualRibbonBoundaryCharacterCoefficient R character) dualKacWard (fun edge => isoradialCriticalMu (Real.pi / 2 - theta edge)) (criticalKacWardRibbonPrefactor (fun edge => Real.pi / 2 - theta edge) dualExceptional)) :
-- imply
  kwIsoradialDualityNormalization DualVertex (fun edge => Real.pi / 2 - theta edge) * (1 - dualKacWard).det = kwIsoradialDualityNormalization PrimalVertex theta * (1 - primalKacWard).det := by
-- proof
  apply StatMech.FrontierA.normalized_isoradialKacWard_duality_of_gaussBonnet R C character hcharacter htotal theta htheta htheta' primalExceptional dualExceptional primalKacWard dualKacWard primalExpansion dualExpansion gaussBonnet

/--
[normalized_isoradialKacWard_duality_of_ribbonCoefficients](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma normalized_isoradialKacWard_duality_of_ribbonCoefficients_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype PrimalVertex]
  [Fintype DualVertex]
  [Fintype Dart]
  [DecidableEq Dart]
  [Fintype DualDart]
  [DecidableEq DualDart]
  [Fintype Q]
  [DecidableEq Q]
  [Fintype Qstar]
  [DecidableEq Qstar]
  {R : RibbonPermutationSystem E Dart}
  {C : CellularRibbonDualData R}
  {Rdual : RibbonPermutationSystem E DualDart}
  {boundaryIdentification : RibbonDualBoundaryIdentification R Rdual}
  {primalKacWard : Matrix Q Q Complex}
  {dualKacWard : Matrix Qstar Qstar Complex}
  {primalCoefficient : CriticalKacWardRibbonCoefficientIdentification R character primalKacWard theta primalExceptional}
  {gaussBonnet : IsoradialDualGaussBonnetParity PrimalVertex DualVertex R C primalExceptional dualExceptional}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (dualCharacter : forall F : Finset E, Fin (Rdual.boundaryComponents F) -> Complex)
  (hcharacter : forall (F : Finset E) (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
  (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
  (dualCharacter_reverse : forall (F : Finset E) (boundary : Fin (Rdual.boundaryComponents F)), dualCharacter F boundary = (character Fᶜ (boundaryIdentification.boundaryEquiv F boundary))⁻¹)
  (theta : E -> Real)
  (htheta : forall edge, 0 < theta edge)
  (htheta' : forall edge, theta edge < Real.pi / 2)
  (primalExceptional : PrimalVertex -> Bool)
  (dualExceptional : DualVertex -> Bool)
  (dualCoefficient : CriticalKacWardRibbonCoefficientIdentification Rdual dualCharacter dualKacWard (fun edge => Real.pi / 2 - theta edge) dualExceptional) :
-- imply
  kwIsoradialDualityNormalization DualVertex (fun edge => Real.pi / 2 - theta edge) * (1 - dualKacWard).det = kwIsoradialDualityNormalization PrimalVertex theta * (1 - primalKacWard).det := by
-- proof
  apply StatMech.FrontierA.normalized_isoradialKacWard_duality_of_ribbonCoefficients R C Rdual character dualCharacter hcharacter htotal boundaryIdentification dualCharacter_reverse theta htheta htheta' primalExceptional dualExceptional primalKacWard dualKacWard primalCoefficient dualCoefficient gaussBonnet

/--
[normalized_isoradialKacWard_duality_of_canonicalDualRibbon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma normalized_isoradialKacWard_duality_of_canonicalDualRibbon_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype PrimalVertex]
  [Fintype DualVertex]
  [Fintype Dart]
  [DecidableEq Dart]
  [Fintype Q]
  [DecidableEq Q]
  [Fintype Qstar]
  [DecidableEq Qstar]
  {R : RibbonPermutationSystem E Dart}
  {C : CellularRibbonDualData R}
  {primalKacWard : Matrix Q Q Complex}
  {dualKacWard : Matrix Qstar Qstar Complex}
  {primalCoefficient : CriticalKacWardRibbonCoefficientIdentification R character primalKacWard theta primalExceptional}
  {oddConeGaussBonnet : IsoradialOddConeGaussBonnetData PrimalVertex DualVertex R C primalExceptional dualExceptional}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (hcharacter : forall (F : Finset E) (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0)
  (htotal : forall F : Finset E, ∏ boundary, character F boundary = 1)
  (theta : E -> Real)
  (htheta : forall edge, 0 < theta edge)
  (htheta' : forall edge, theta edge < Real.pi / 2)
  (primalExceptional : PrimalVertex -> Bool)
  (dualExceptional : DualVertex -> Bool)
  (dualCoefficient : CriticalKacWardRibbonCoefficientIdentification R.dualRibbonSystem (R.dualBoundaryCharacter character) dualKacWard (fun edge => Real.pi / 2 - theta edge) dualExceptional) :
-- imply
  kwIsoradialDualityNormalization DualVertex (fun edge => Real.pi / 2 - theta edge) * (1 - dualKacWard).det = kwIsoradialDualityNormalization PrimalVertex theta * (1 - primalKacWard).det := by
-- proof
  apply StatMech.FrontierA.normalized_isoradialKacWard_duality_of_canonicalDualRibbon R C character hcharacter htotal theta htheta htheta' primalExceptional dualExceptional primalKacWard dualKacWard primalCoefficient dualCoefficient oddConeGaussBonnet

/--
[CriticalIsoradialDualityCertificate.normalized_det_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma normalized_det_eq_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype PrimalVertex]
  [Fintype DualVertex]
  [Fintype Dart]
  [DecidableEq Dart]
  [Fintype Q]
  [DecidableEq Q]
  [Fintype Qstar]
  [DecidableEq Qstar]
  {R : RibbonPermutationSystem E Dart}
  {C : CellularRibbonDualData R}
  {primalKacWard : Matrix Q Q Complex}
  {dualKacWard : Matrix Qstar Qstar Complex}
  {certificate : CriticalIsoradialDualityCertificate PrimalVertex DualVertex Dart Q Qstar R C character theta primalExceptional dualExceptional primalKacWard dualKacWard}
-- given
  (character : forall F : Finset E, Fin (R.boundaryComponents F) -> Complex)
  (theta : E -> Real)
  (primalExceptional : PrimalVertex -> Bool)
  (dualExceptional : DualVertex -> Bool) :
-- imply
  kwIsoradialDualityNormalization DualVertex (fun edge => Real.pi / 2 - theta edge) * (1 - dualKacWard).det = kwIsoradialDualityNormalization PrimalVertex theta * (1 - primalKacWard).det := by
-- proof
  apply StatMech.FrontierA.CriticalIsoradialDualityCertificate.normalized_det_eq R C character theta primalExceptional dualExceptional primalKacWard dualKacWard certificate

/--
[normalized_isoradialKacWard_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean)
-/
@[path]
private lemma normalized_isoradialKacWard_duality_eq_2
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype DualVertex]
  [Fintype Q]
  [DecidableEq Q]
  [Fintype Qstar]
  [DecidableEq Qstar]
  {embedding : FiniteCellularGraphEmbedding G}
  {primalKacWard : Matrix Q Q Complex}
  {dualKacWard : Matrix Qstar Qstar Complex}
  {primalExpansion : CriticalKacWardRibbonCoefficientIdentification embedding.ribbonSystem character primalKacWard theta primalExceptional}
-- given
  (dualVertexCount_eq : embedding.faceCount = Fintype.card DualVertex)
  (character : forall F : Finset (finiteGraphEdge G), Fin (embedding.ribbonSystem.boundaryComponents F) -> Complex)
  (hcharacter : forall (F : Finset (finiteGraphEdge G)) (boundary : Fin (embedding.ribbonSystem.boundaryComponents F)), character F boundary ≠ 0)
  (htotal : forall F : Finset (finiteGraphEdge G), ∏ boundary, character F boundary = 1)
  (theta : finiteGraphEdge G -> Real)
  (htheta : forall edge, 0 < theta edge)
  (htheta' : forall edge, theta edge < Real.pi / 2)
  (primalExceptional : V -> Bool)
  (dualExceptional : DualVertex -> Bool)
  (primalConeIndex : V -> Nat)
  (dualConeIndex : DualVertex -> Nat)
  (primalExceptional_iff : forall vertex, primalExceptional vertex = true ↔ primalConeIndex vertex % 2 = 1)
  (dualExceptional_iff : forall vertex, dualExceptional vertex = true ↔ dualConeIndex vertex % 2 = 1)
  (coneIndexGaussBonnet : (∑ vertex : V, primalConeIndex vertex) + (∑ vertex : DualVertex, dualConeIndex vertex) + 1 = embedding.genus)
  (dualExpansion : CriticalKacWardRibbonCoefficientIdentification embedding.ribbonSystem.dualRibbonSystem (embedding.ribbonSystem.dualBoundaryCharacter character) dualKacWard (fun edge => Real.pi / 2 - theta edge) dualExceptional) :
-- imply
  kwIsoradialDualityNormalization DualVertex (fun edge => Real.pi / 2 - theta edge) * (1 - dualKacWard).det = kwIsoradialDualityNormalization V theta * (1 - primalKacWard).det := by
-- proof
  apply StatMech.FrontierA.FiniteCellularGraphEmbedding.normalized_isoradialKacWard_duality G embedding dualVertexCount_eq character hcharacter htotal theta htheta htheta' primalExceptional dualExceptional primalConeIndex dualConeIndex primalExceptional_iff dualExceptional_iff coneIndexGaussBonnet primalKacWard dualKacWard primalExpansion dualExpansion


-- created on 2026-10-23
