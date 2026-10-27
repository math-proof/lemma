import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorToExponent
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteCurrentMassBridgeInputs


/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (honeJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale hlim hdecay hfinite honeJ hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale hlim hdecay hfinite honeJ hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (honeJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale hlim hdecay hSimon honeJ hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale hlim hdecay hSimon honeJ hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hcases : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale hlim hdecay hfinite hcases hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale hlim hdecay hfinite hcases hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hcases : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale hlim hdecay hSimon hcases hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale hlim hdecay hSimon hcases hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hcases : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale hlim hdecay hfinite hcases hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale hlim hdecay hfinite hcases hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hcases : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale hlim hdecay hSimon hcases hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale hlim hdecay hSimon hcases hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hcases : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale hlim hdecay hfinite hcases hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale hlim hdecay hfinite hcases hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hcases : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale hlim hdecay hSimon hcases hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale hlim hdecay hSimon hcases hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hcases : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale hlim hdecay hfinite hcases hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale hlim hdecay hfinite hcases hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hcases : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale hlim hdecay hSimon hcases hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale hlim hdecay hSimon hcases hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsProfileDoubleScale hlim hdecay hfinite hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hrows : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsProfileDoubleScale hlim hdecay hSimon hrows hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (honeJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocalProfileDoubleScale hlim hdecay hfinite honeJ hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocalProfileDoubleScale hlim hdecay hfinite honeJ hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (honeJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocalProfileDoubleScale hlim hdecay hSimon honeJ hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocalProfileDoubleScale hlim hdecay hSimon honeJ hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal)
  (hdiagYJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal)
  (hstrictYJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesLocalProfileDoubleScale hlim hdecay hfinite hstrictZJ hdiagYJ hstrictYJ hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesLocalProfileDoubleScale hlim hdecay hfinite hstrictZJ hdiagYJ hstrictYJ hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal)
  (hdiagYJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal)
  (hstrictYJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesLocalProfileDoubleScale hlim hdecay hSimon hstrictZJ hdiagYJ hstrictYJ hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesLocalProfileDoubleScale hlim hdecay hSimon hstrictZJ hdiagYJ hstrictYJ hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJYLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJYLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJYLocalProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYJ hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJYLocalProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYJ hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJYLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJYLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJYLocalProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYJ hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJYLocalProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYJ hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYJ hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYJ hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYJ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYJ hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYJ hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYBranch : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYBranch hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYBranch hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYBranch : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYBranch hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYBranch hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYComponent : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYComponent hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYComponent hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYComponent : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYComponent hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYComponent hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYBounds : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYBounds hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYBounds hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYBounds : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYBounds hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYBounds hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYBounds : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYBounds hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYBounds hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYBounds : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYBounds hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYBounds hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYBounds : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical)
  (hstrictYSplit : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYBounds hstrictYSplit hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYBounds hstrictYSplit hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYBounds : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical)
  (hstrictYSplit : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYBounds hstrictYSplit hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYBounds hstrictYSplit hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYBounds : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYBounds hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYBounds hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYBounds : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYBounds hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYBounds hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hselected : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hselected hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hselected hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hselected : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hselected hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hselected hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffMajorantBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffMajorantBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffMajorantBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffMajorantBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffExplicitCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffExplicitCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffExplicitCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffExplicitCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAndExpectationJRatioGapProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAndExpectationJRatioGapProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (htable : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsPositiveSubcritical)
  (hstrictYRatio : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAndExpectationJRatioGapProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY htable hstrictYRatio hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYVertexEdge : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYVertexEdge hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictYVertexEdge hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictYVertexEdge : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYVertexEdge hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictYVertexEdge hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
  (hJsplit : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hJsplit hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsExpectationJSplitProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hempty hinner hJsplit hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsExpectationJSplitProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsExpectationJSplitProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hempty : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
  (hinner : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
  (hJsplit : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hJsplit hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsExpectationJSplitProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hempty hinner hJsplit hprofile C hagree hpower


-- created on 2026-10-23
