import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample
open Filter StatMech StatMech.Exact3D StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample


/--
[ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcritical hcmp hdecay hEq

/--
[ising3D_liminf_hasCriticalNu_from_freeQ2ExactPositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_liminf_hasCriticalNu_from_freeQ2ExactPositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_liminf_hasCriticalNu_from_freeQ2ExactPositiveSubcritical hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcritical hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcritical hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical hprofile hEq

/--
[ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical_components_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical_components hlim hsameMass hcombine hEq

/--
[ising3D_hasCriticalNu_from_freeQ2ProfileSeparate_splitSubexpProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2ProfileSeparate_splitSubexpProfile_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile hlim hfixed hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile hlim hfixed hprofile)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2ProfileSeparate_splitSubexpProfile hlim hfixed hprofile hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexPointwise_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_boundaryVertexPointwise hlim hfixed hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_boundaryVertexPointwise hlim hfixed hprofile)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexPointwise hlim hfixed hprofile hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryProfileComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryProfileComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileSubexpComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileSubexpComparisonToXAxis hlim hfixed hcompare)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryProfileComparison hlim hfixed hcompare hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryProfileFiniteVolumePolynomialComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryProfileFiniteVolumePolynomialComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryProfileFiniteVolumePolynomialComparison hlim hfixed hcompare hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryProfileScaledFiniteVolumePolynomialComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryProfileScaledFiniteVolumePolynomialComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryProfileScaledFiniteVolumePolynomialComparison hlim hfixed hcompare hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_subexpComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_subexpComparisonToXAxis hlim hfixed hcompare)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexComparison hlim hfixed hcompare hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexFiniteVolumePolynomialComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexFiniteVolumePolynomialComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_finiteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_finiteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexFiniteVolumePolynomialComparison hlim hfixed hcompare hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexRate_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrate : FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_polynomialRateWithXAxisLogRate hlim hfixed hrate) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_polynomialRateWithXAxisLogRate hlim hfixed hrate)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexRate hlim hfixed hrate hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexDirectionalRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexDirectionalRate_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hdir : FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_directionalRate hlim hfixed hdir) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_directionalRate hlim hfixed hdir)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexDirectionalRate hlim hfixed hdir hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexConvexSurfaceTensionUpper_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_convexSurfaceTensionUpper hlim hfixed htension) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_convexSurfaceTensionUpper hlim hfixed htension)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexConvexSurfaceTensionUpper hlim hfixed htension hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexActualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexActualConvexSurfaceTensionUpper_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_actualConvexSurfaceTensionUpper hlim hfixed htension) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_actualConvexSurfaceTensionUpper hlim hfixed htension)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexActualConvexSurfaceTensionUpper hlim hfixed htension hEq

/--
[ising3D_liminf_hasCriticalNu_from_freeQ2ProfileSeparate_splitSubexpProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_liminf_hasCriticalNu_from_freeQ2ProfileSeparate_splitSubexpProfile_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile hlim hfixed hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_liminf_hasCriticalNu_from_freeQ2ProfileSeparate_splitSubexpProfile hlim hfixed hprofile hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcritical hbad hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcritical hbad hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcritical hbad hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Exact hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Exact hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Subexp hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Subexp hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass hprofile hEq

/--
[ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass_components_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass_components hlim hsameMass hcombine hEq

/--
[ising3D_hasCriticalNu_from_freeQ2ProfileSeparateMass_splitSubexpProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2ProfileSeparateMass_splitSubexpProfile_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile hlim hfixed hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile hlim hfixed hprofile)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2ProfileSeparateMass_splitSubexpProfile hlim hfixed hprofile hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexPointwiseMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexPointwiseMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_boundaryVertexPointwise hlim hfixed hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_boundaryVertexPointwise hlim hfixed hprofile)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexPointwiseMass hlim hfixed hprofile hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexComparisonMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexComparisonMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_subexpComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_subexpComparisonToXAxis hlim hfixed hcompare)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexComparisonMass hlim hfixed hcompare hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryProfileFiniteVolumePolynomialComparisonMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryProfileFiniteVolumePolynomialComparisonMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_profileFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_profileFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryProfileFiniteVolumePolynomialComparisonMass hlim hfixed hcompare hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonMass hlim hfixed hcompare hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexFiniteVolumePolynomialComparisonMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexFiniteVolumePolynomialComparisonMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexFiniteVolumePolynomialComparisonMass hlim hfixed hcompare hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexRateMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexRateMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrate : FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate hlim hfixed hrate) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate hlim hfixed hrate)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexRateMass hlim hfixed hrate hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexDirectionalRateMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexDirectionalRateMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hdir : FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_directionalRate hlim hfixed hdir) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_directionalRate hlim hfixed hdir)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexDirectionalRateMass hlim hfixed hdir hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexConvexSurfaceTensionUpperMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexConvexSurfaceTensionUpperMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper hlim hfixed htension) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper hlim hfixed htension)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexConvexSurfaceTensionUpperMass hlim hfixed htension hEq

/--
[ising3D_hasCriticalNu_from_freeQ2BoundaryVertexActualConvexSurfaceTensionUpperMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2BoundaryVertexActualConvexSurfaceTensionUpperMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper hlim hfixed htension) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper hlim hfixed htension)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2BoundaryVertexActualConvexSurfaceTensionUpperMass hlim hfixed htension hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2Exact hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2Exact hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcriticalMass hbad hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcriticalMass hbad hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass hbad hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcritical_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcritical_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcritical_belowBetaC hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcritical_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcritical_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcritical_belowBetaC hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcritical_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcritical_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcritical_belowBetaC hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcritical_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcritical_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcritical_belowBetaC hbad hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcritical_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcritical_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcritical_belowBetaC hbad hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcritical_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcritical_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcritical_belowBetaC hbad hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass_belowBetaC hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass_belowBetaC hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass_belowBetaC hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass_restrictedCylinderComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2ExactPositiveSubcriticalMass_restrictedCylinderComparison hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass_restrictedCylinderComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2SubexpPositiveSubcriticalMass_restrictedCylinderComparison hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass_restrictedCylinderComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_freeQ2TwoSidedPositiveSubcriticalMass_restrictedCylinderComparison hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcriticalMass_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcriticalMass_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2ExactPositiveSubcriticalMass_belowBetaC hbad hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcriticalMass_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcriticalMass_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2SubexpPositiveSubcriticalMass_belowBetaC hbad hcmp hdecay hEq

/--
[ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay)) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.ising3D_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass_belowBetaC hbad hcmp hdecay hEq

/--
[closedBall_bridge_from_freeQ2ExactPositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_bridge_from_freeQ2ExactPositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_bridge_from_freeQ2ExactPositiveSubcritical hpred hcmp hdecay hEq

/--
[closedBall_valid_from_freeQ2ExactPositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_valid_from_freeQ2ExactPositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_valid_from_freeQ2ExactPositiveSubcritical hpred hcmp hdecay hEq

/--
[closedBall_hasCriticalNu_from_freeQ2ExactPositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_hasCriticalNu_from_freeQ2ExactPositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay)) (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_hasCriticalNu_from_freeQ2ExactPositiveSubcritical hpred hcmp hdecay hEq

/--
[closedBall_bridge_from_freeQ2ProfileSeparatePositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_bridge_from_freeQ2ProfileSeparatePositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_bridge_from_freeQ2ProfileSeparatePositiveSubcritical hpred hprofile hEq

/--
[closedBall_valid_from_freeQ2ProfileSeparatePositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_valid_from_freeQ2ProfileSeparatePositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_valid_from_freeQ2ProfileSeparatePositiveSubcritical hpred hprofile hEq

/--
[closedBall_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hprofile)) (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcritical hpred hprofile hEq

/--
[closedBall_bridge_from_freeQ2ProfileSeparatePositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_bridge_from_freeQ2ProfileSeparatePositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_bridge_from_freeQ2ProfileSeparatePositiveSubcriticalMass hpred hprofile hEq

/--
[closedBall_valid_from_freeQ2ProfileSeparatePositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_valid_from_freeQ2ProfileSeparatePositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_valid_from_freeQ2ProfileSeparatePositiveSubcriticalMass hpred hprofile hEq

/--
[closedBall_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hprofile : FreeQ2ProfileSeparatePositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate hprofile)) (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_hasCriticalNu_from_freeQ2ProfileSeparatePositiveSubcriticalMass hpred hprofile hEq

/--
[closedBall_bridge_from_freeQ2ProfileSeparate_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_bridge_from_freeQ2ProfileSeparate_components_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_bridge_from_freeQ2ProfileSeparate_components hpred hlim hsameMass hcombine hEq

/--
[closedBall_valid_from_freeQ2ProfileSeparate_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_valid_from_freeQ2ProfileSeparate_components_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_valid_from_freeQ2ProfileSeparate_components hpred hlim hsameMass hcombine hEq

/--
[closedBall_hasCriticalNu_from_freeQ2ProfileSeparate_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_hasCriticalNu_from_freeQ2ProfileSeparate_components_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine)) (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_hasCriticalNu_from_freeQ2ProfileSeparate_components hpred hlim hsameMass hcombine hEq

/--
[closedBall_bridge_from_scaledProfileFiniteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_bridge_from_scaledProfileFiniteVolumePolynomial_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_bridge_from_scaledProfileFiniteVolumePolynomial hpred hlim hfixed hcompare hEq

/--
[closedBall_valid_from_scaledProfileFiniteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_valid_from_scaledProfileFiniteVolumePolynomial_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_valid_from_scaledProfileFiniteVolumePolynomial hpred hlim hfixed hcompare hEq

/--
[closedBall_hasCriticalNu_from_scaledProfileFiniteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_hasCriticalNu_from_scaledProfileFiniteVolumePolynomial_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_hasCriticalNu_from_scaledProfileFiniteVolumePolynomial hpred hlim hfixed hcompare hEq

/--
[closedBall_bridge_from_scaledProfileFiniteVolumePolynomialMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_bridge_from_scaledProfileFiniteVolumePolynomialMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_bridge_from_scaledProfileFiniteVolumePolynomialMass hpred hlim hfixed hcompare hEq

/--
[closedBall_valid_from_scaledProfileFiniteVolumePolynomialMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_valid_from_scaledProfileFiniteVolumePolynomialMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_valid_from_scaledProfileFiniteVolumePolynomialMass hpred hlim hfixed hcompare hEq

/--
[closedBall_hasCriticalNu_from_scaledProfileFiniteVolumePolynomialMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_hasCriticalNu_from_scaledProfileFiniteVolumePolynomialMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare)) (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_hasCriticalNu_from_scaledProfileFiniteVolumePolynomialMass hpred hlim hfixed hcompare hEq

/--
[closedBall_bridge_from_freeQ2ProfileSeparateMass_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_bridge_from_freeQ2ProfileSeparateMass_components_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_bridge_from_freeQ2ProfileSeparateMass_components hpred hlim hsameMass hcombine hEq

/--
[closedBall_valid_from_freeQ2ProfileSeparateMass_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_valid_from_freeQ2ProfileSeparateMass_components_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_valid_from_freeQ2ProfileSeparateMass_components hpred hlim hsameMass hcombine hEq

/--
[closedBall_hasCriticalNu_from_freeQ2ProfileSeparateMass_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_hasCriticalNu_from_freeQ2ProfileSeparateMass_components_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine)) (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_hasCriticalNu_from_freeQ2ProfileSeparateMass_components hpred hlim hsameMass hcombine hEq

/--
[tableClosedBall_bridge_from_wiredQ2TwoSidedPositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma tableClosedBall_bridge_from_wiredQ2TwoSidedPositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent = C.predictedExponent)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.tableClosedBall_bridge_from_wiredQ2TwoSidedPositiveSubcriticalMass hpred hbad hcmp hdecay hEq

/--
[tableClosedBall_valid_from_wiredQ2TwoSidedPositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma tableClosedBall_valid_from_wiredQ2TwoSidedPositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent = C.predictedExponent)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.tableClosedBall_valid_from_wiredQ2TwoSidedPositiveSubcriticalMass hpred hbad hcmp hdecay hEq

/--
[tableClosedBall_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma tableClosedBall_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent = C.predictedExponent)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay)) ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.tableClosedBall_hasCriticalNu_from_wiredQ2TwoSidedPositiveSubcriticalMass hpred hbad hcmp hdecay hEq

/--
[closedBall_bridge_from_freeQ2ExactPositiveSubcritical_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_bridge_from_freeQ2ExactPositiveSubcritical_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_bridge_from_freeQ2ExactPositiveSubcritical_belowBetaC hpred hcmp hdecay hEq

/--
[closedBall_valid_from_freeQ2ExactPositiveSubcritical_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_valid_from_freeQ2ExactPositiveSubcritical_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_valid_from_freeQ2ExactPositiveSubcritical_belowBetaC hpred hcmp hdecay hEq

/--
[closedBall_hasCriticalNu_from_freeQ2ExactPositiveSubcritical_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma closedBall_hasCriticalNu_from_freeQ2ExactPositiveSubcritical_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = C.predictedExponent)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLength (freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay)) (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.closedBall_hasCriticalNu_from_freeQ2ExactPositiveSubcritical_belowBetaC hpred hcmp hdecay hEq

/--
[tableClosedBall_bridge_from_wiredQ2TwoSidedMass_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma tableClosedBall_bridge_from_wiredQ2TwoSidedMass_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent = C.predictedExponent)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.tableClosedBall_bridge_from_wiredQ2TwoSidedMass_belowBetaC hpred hbad hcmp hdecay hEq

/--
[tableClosedBall_valid_from_wiredQ2TwoSidedMass_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma tableClosedBall_valid_from_wiredQ2TwoSidedMass_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent = C.predictedExponent)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay)) := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.tableClosedBall_valid_from_wiredQ2TwoSidedMass_belowBetaC hpred hbad hcmp hdecay hEq

/--
[tableClosedBall_hasCriticalNu_from_wiredQ2TwoSidedMass_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2AnalyticBridgeExample.lean)
-/
@[path]
private lemma tableClosedBall_hasCriticalNu_from_wiredQ2TwoSidedMass_belowBetaC_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hpred : ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent = C.predictedExponent)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay) β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay)) ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPositiveSubcriticalQ2AnalyticBridgeExample.tableClosedBall_hasCriticalNu_from_wiredQ2TwoSidedMass_belowBetaC hpred hbad hcmp hdecay hEq


-- created on 2026-10-23
