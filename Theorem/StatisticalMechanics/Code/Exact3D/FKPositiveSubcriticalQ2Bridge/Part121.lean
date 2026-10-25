/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part123
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem freeQ2ProfileSeparatePositiveSubcritical_of_components
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical := by
  intro β hβpos hβc
  rcases hsameMass β hβpos hβc with
    ⟨Alo, AfkHi, AprofHi, mass, hmass, hconn, hprofileHi⟩
  rcases hcombine β hβpos hβc AfkHi AprofHi with
    ⟨Ahi, hAhiPos, hAhiLog, hprefCombine⟩
  exact ⟨hlim β hβpos hβc, Alo, AfkHi, AprofHi, Ahi, mass, hmass,
    hconn, hAhiPos, hAhiLog, hprofileHi, hprefCombine⟩


theorem freeQ2ProfileSeparatePositiveSubcritical_of_splitComponents
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparatePositiveSubcritical_of_components hlim
    (freeQ2FixedInnerProfileSameMassPositiveSubcritical_of_fixedInner_profile
      hfixed hprofile)
    hcombine


theorem freeQ2ProfileSeparate_of_freeFVQ2TwoSided_profile_combine
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparatePositiveSubcritical_of_splitComponents hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hprofile hcombine


theorem freeQ2ProfileSeparatePositiveSubcritical_of_splitSubexpProfile
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical := by
  intro β hβpos hβc
  rcases hfixed β hβpos hβc with ⟨Alo, AfkHi, mass, hmass, hconn⟩
  rcases hprofile β hβpos hβc Alo AfkHi mass hmass hconn with
    ⟨AprofHi, hAprof, hprofileHi⟩
  let Ahi : ℕ → ℝ := fun n => AfkHi n + AprofHi n
  have hAfk : PositiveSubexponentialPrefactor AfkHi :=
    ⟨hconn.2.1, hconn.2.2.2.1⟩
  have hAhi : PositiveSubexponentialPrefactor Ahi :=
    PositiveSubexponentialPrefactor.add hAfk hAprof
  exact ⟨hlim β hβpos hβc, Alo, AfkHi, AprofHi, Ahi, mass, hmass,
    hconn, hAhi.1, hAhi.2, hprofileHi, Eventually.of_forall fun _ => le_rfl⟩


theorem
    freeQ2ProfileSeparatePositiveSubcritical_of_freeFVQ2TwoSided_splitSubexpProfile
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparatePositiveSubcritical_of_splitSubexpProfile hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hprofile


theorem freeQ2ProfileSeparate_of_boundaryVertexPointwise
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparatePositiveSubcritical_of_splitSubexpProfile hlim hfixed
    (freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexPointwise hprofile)


theorem freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparatePositiveSubcritical_of_splitSubexpProfile hlim hfixed
    (freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis
      hcompare)


theorem freeQ2ProfileSeparate_of_profilePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profilePolynomialComparisonToXAxis
      hcompare)


theorem freeQ2ProfileSeparate_of_profileFiniteVolumeComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumeComparisonToXAxis
      hcompare)


theorem freeQ2ProfileSeparate_of_profileFiniteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumePolynomial
      hcompare)


theorem
    freeQ2ProfileSeparate_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileScaledFiniteVolumePolynomial
      hcompare)


theorem freeQ2ProfileSeparate_of_vertexDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_vertexDoubleScale hcompare)


theorem freeQ2ProfileSeparate_of_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_profileDoubleScale hcompare)


theorem freeQ2ProfileSeparate_of_simonFreeSum_doubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_doubledBoxPolynomialProjection
      hsimon hprojection)


theorem
    freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
      hsimon hprojection)


theorem freeQ2ProfileSeparate_of_simonFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_projection
      hsimon hprojection)


theorem freeQ2ProfileSeparate_of_simonFreeSum_doubledBoxProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_doubledBoxProjection
      hsimon hprojection)


theorem freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceProjection
      hsimon hprojection)


theorem freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeProjection
      hsimon hprojection)


theorem
    freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
      hsimon hstep)


theorem
    freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    hlim hfixed hsimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_branches
      hstrict hdiag)


theorem
    freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
      hfinite hprojection)


theorem
    freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
      hfinite hprojection)


theorem freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_projection
      hfinite hprojection)


theorem freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_doubledBoxProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_doubledBoxProjection
      hfinite hprojection)


theorem freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceProjection
      hfinite hprojection)


theorem
    freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection
      hfinite hprojection)


theorem
    freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
      hfinite hstep)


theorem
    freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    hlim hfixed hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_branches
      hstrict hdiag)


theorem
    freeQ2ProfileSeparate_of_finiteIsingSimon_doubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem
    freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection

set_option linter.style.longLine false in


theorem
    freeQ2ProfileSeparate_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale
      hsimon hstrict hdiag hprofile)

set_option linter.style.longLine false in


theorem
    freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale
    hlim hfixed (freeQ2BoundaryProfileSimonFreeSum_of_finiteFK hfinite)
    hstrict hdiag hprofile

set_option linter.style.longLine false in


theorem
    freeQ2ProfileSeparate_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hstrict hdiag hprofile


theorem freeQ2ProfileSeparate_of_finiteIsingSimon_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_projection hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem freeQ2ProfileSeparate_of_finiteIsingSimon_doubledBoxProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_doubledBoxProjection
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceProjection
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem
    freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem
    freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hstep


theorem
    freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep
    hlim hfixed hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_branches
      hstrict hdiag)


theorem freeQ2ProfileSeparate_of_subexpComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_boundaryVertexSubexpComparisonToXAxis
      hcompare)


theorem freeQ2ProfileSeparate_of_polynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_polynomialComparisonToXAxis
      hcompare)


theorem freeQ2ProfileSeparate_of_finiteVolumeComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumeComparisonToXAxis
      hcompare)


theorem freeQ2ProfileSeparate_of_finiteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumePolynomialComparisonToXAxis
      hcompare)


theorem
    freeQ2ProfileSeparate_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_finiteVolumePolynomialComparisonToXAxis hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hcompare


theorem freeQ2ProfileSeparate_of_envelopeAtLeastMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (henv :
      FreeQ2BoundaryVertexEnvelopeAtLeastMassPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_boundaryVertexPointwise hlim hfixed
    (freeQ2BoundaryVertexPointwise_of_envelopeAtLeastMass henv)


theorem freeQ2ProfileSeparate_of_polynomialAtLeastMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hpoly :
      FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_boundaryVertexPointwise hlim hfixed
    (freeQ2BoundaryVertexPointwise_of_polynomialAtLeastMass hpoly)


theorem freeQ2ProfileSeparate_of_polynomialRateWithXAxisLogRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_polynomialAtLeastMass hlim hfixed
    (freeQ2BoundaryVertexPolynomialAtLeastMass_of_polynomialRateWithXAxisLogRate
      hrate)


theorem freeQ2ProfileSeparate_of_directionalRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_polynomialRateWithXAxisLogRate hlim hfixed
    (freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_directionalRate
      hdir)


theorem freeQ2ProfileSeparate_of_convexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_directionalRate hlim hfixed
    (freeQ2BoundaryVertexDirectionalRate_of_convexSurfaceTensionUpper
      htension)


theorem freeQ2ProfileSeparate_of_actualConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_directionalRate hlim hfixed
    (freeQ2BoundaryVertexDirectionalRate_of_actualConvexSurfaceTensionUpper
      htension)


theorem freeQ2ProfileSeparate_of_freeFVQ2TwoSided_boundaryPointwise
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_boundaryVertexPointwise hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hprofile


theorem freeQ2ProfileSeparate_of_freeFVQ2TwoSided_subexpComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
    FreeQ2ProfileSeparatePositiveSubcritical :=
  freeQ2ProfileSeparate_of_subexpComparisonToXAxis hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hcompare


theorem freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  rcases (freeQ2ProfileSeparatePositiveSubcritical_of_components
      hlim hsameMass hcombine) β hβpos hβc with
    ⟨hIsing, Alo, AfkHi, AprofHi, Ahi, mass, hmass, hconn,
      hAhiPos, hAhiLog, hProfileHi, hCombine⟩
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate
      hβpos hIsing hconn hAhiPos hAhiLog hProfileHi hCombine⟩


theorem freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components
      hlim hsameMass hcombine)


theorem freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitComponents
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components hlim
    (freeQ2FixedInnerProfileSameMassPositiveSubcritical_of_fixedInner_profile
      hfixed hprofile)
    hcombine


theorem freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitComponents
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical)
    (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitComponents
      hlim hfixed hprofile hcombine)


theorem freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  rcases (freeQ2ProfileSeparatePositiveSubcritical_of_splitSubexpProfile
      hlim hfixed hprofile) β hβpos hβc with
    ⟨hIsing, Alo, AfkHi, AprofHi, Ahi, mass, hmass, hconn,
      hAhiPos, hAhiLog, hProfileHi, hCombine⟩
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate
      hβpos hIsing hconn hAhiPos hAhiLog hProfileHi hCombine⟩


theorem freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile
      hlim hfixed hprofile)


theorem freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_splitSubexpProfile
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hprofile


theorem freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_splitSubexpProfile
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_splitSubexpProfile
      hlim hdecay hprofile)


theorem freePosSubcriticalMassBridge_of_boundaryVertexPointwise
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile hlim
    hfixed
    (freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexPointwise hprofile)


theorem freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile hlim
    hfixed
    (freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis
      hcompare)


theorem freePosSubcriticalMassBridge_of_profilePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profilePolynomialComparisonToXAxis
      hcompare)


theorem freePosSubcriticalMassBridge_of_profileFiniteVolumeComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumeComparisonToXAxis
      hcompare)


theorem
    freePosSubcriticalMassBridge_of_profileFiniteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumePolynomial
      hcompare)


theorem
    freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileScaledFiniteVolumePolynomial
      hcompare)


theorem freePosSubcriticalMassBridge_of_vertexDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_vertexDoubleScale hcompare)


theorem freePosSubcriticalMassBridge_of_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_profileDoubleScale hcompare)


theorem freePosSubcriticalMassBridge_of_simonFreeSum_doubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_doubledBoxPolynomialProjection
      hsimon hprojection)


theorem
    freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
      hsimon hprojection)


theorem freePosSubcriticalMassBridge_of_simonFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_projection
      hsimon hprojection)


theorem freePosSubcriticalMassBridge_of_simonFreeSum_doubledBoxProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_doubledBoxProjection
      hsimon hprojection)


theorem freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceProjection
      hsimon hprojection)


theorem
    freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeProjection
      hsimon hprojection)


theorem
    freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
      hsimon hstep)


theorem
    freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    hlim hfixed hsimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_branches
      hstrict hdiag)


theorem
    freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
      hfinite hprojection)


theorem
    freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
      hfinite hprojection)


theorem freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_projection
      hfinite hprojection)


theorem freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_doubledBoxProjection
      hfinite hprojection)


theorem freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceProjection
      hfinite hprojection)


theorem
    freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection
      hfinite hprojection)


theorem
    freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed
    (freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
      hfinite hstep)


theorem
    freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    hlim hfixed hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_branches
      hstrict hdiag)


theorem
    freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem
    freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection

set_option linter.style.longLine false in


theorem
    freePosSubcriticalMassBridge_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    hlim hfixed
    (freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale
      hsimon hstrict hdiag hprofile)

set_option linter.style.longLine false in


theorem
    freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale
    hlim hfixed (freeQ2BoundaryProfileSimonFreeSum_of_finiteFK hfinite)
    hstrict hdiag hprofile

set_option linter.style.longLine false in


theorem
    freePosSubcriticalMassBridge_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hstrict hdiag hprofile


theorem freePosSubcriticalMassBridge_of_finiteIsingSimon_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_projection hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxProjection
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceProjection
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem
    freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hprojection


theorem
    freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    hlim hfixed
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon)
    hstep


theorem
    freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep
    hlim hfixed hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_branches
      hstrict hdiag)


theorem freePosSubcriticalMassBridge_of_subexpComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_boundaryVertexSubexpComparisonToXAxis
      hcompare)


theorem freePosSubcriticalMassBridge_of_polynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_polynomialComparisonToXAxis
      hcompare)


theorem freePosSubcriticalMassBridge_of_finiteVolumeComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumeComparisonToXAxis
      hcompare)


theorem freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis hlim hfixed
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumePolynomialComparisonToXAxis
      hcompare)


theorem freePosSubcriticalMassBridge_of_envelopeAtLeastMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (henv :
      FreeQ2BoundaryVertexEnvelopeAtLeastMassPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryVertexPointwise hlim hfixed
    (freeQ2BoundaryVertexPointwise_of_envelopeAtLeastMass henv)


theorem freePosSubcriticalMassBridge_of_polynomialAtLeastMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hpoly :
      FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryVertexPointwise hlim hfixed
    (freeQ2BoundaryVertexPointwise_of_polynomialAtLeastMass hpoly)


theorem freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_polynomialAtLeastMass hlim hfixed
    (freeQ2BoundaryVertexPolynomialAtLeastMass_of_polynomialRateWithXAxisLogRate
      hrate)


theorem freePosSubcriticalMassBridge_of_directionalRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate hlim hfixed
    (freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_directionalRate
      hdir)


theorem freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_directionalRate hlim hfixed
    (freeQ2BoundaryVertexDirectionalRate_of_convexSurfaceTensionUpper
      htension)


theorem freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_directionalRate hlim hfixed
    (freeQ2BoundaryVertexDirectionalRate_of_actualConvexSurfaceTensionUpper
      htension)


theorem freePosSubcriticalCorrBridge_of_boundaryVertexPointwise
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_boundaryVertexPointwise
      hlim hfixed hprofile)


theorem freePosSubcriticalCorrBridge_of_profileSubexpComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis
      hlim hfixed hcompare)


theorem freePosSubcriticalCorrBridge_of_profilePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_profilePolynomialComparisonToXAxis
      hlim hfixed hcompare)


theorem freePosSubcriticalCorrBridge_of_profileFiniteVolumeComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_profileFiniteVolumeComparisonToXAxis
      hlim hfixed hcompare)


theorem
    freePosSubcriticalCorrBridge_of_profileFiniteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_profileFiniteVolumePolynomialComparisonToXAxis
      hlim hfixed hcompare)


theorem
    freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
      hlim hfixed hcompare)


theorem freePosSubcriticalCorrBridge_of_vertexDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_vertexDoubleScale hlim hfixed hcompare)


theorem freePosSubcriticalCorrBridge_of_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed hcompare)


theorem freePosSubcriticalCorrBridge_of_simonFreeSum_doubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_simonFreeSum_doubledBoxPolynomialProjection
      hlim hfixed hsimon hprojection)


theorem
    freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
      hlim hfixed hsimon hprojection)


theorem freePosSubcriticalCorrBridge_of_simonFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_simonFreeSum_projection
      hlim hfixed hsimon hprojection)


theorem freePosSubcriticalCorrBridge_of_simonFreeSum_doubledBoxProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_simonFreeSum_doubledBoxProjection
      hlim hfixed hsimon hprojection)


theorem freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceProjection
      hlim hfixed hsimon hprojection)


theorem
    freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeProjection
      hlim hfixed hsimon hprojection)


theorem
    freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
      hlim hfixed hsimon hstep)


theorem
    freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches
      hlim hfixed hsimon hstrict hdiag)


theorem
    freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
      hlim hfixed hfinite hprojection)


theorem
    freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
      hlim hfixed hfinite hprojection)


theorem freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_projection
      hlim hfixed hfinite hprojection)


theorem
    freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_doubledBoxProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxProjection
      hlim hfixed hfinite hprojection)


theorem
    freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceProjection
      hlim hfixed hfinite hprojection)


theorem
    freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection
      hlim hfixed hfinite hprojection)


theorem
    freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep
      hlim hfixed hfinite hstep)


theorem
    freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches
      hlim hfixed hfinite hstrict hdiag)


theorem
    freePosSubcriticalCorrBridge_of_finiteIsingSimon_doubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxPolynomialProjection
      hlim hfixed hSimon hprojection)


theorem
    freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection
      hlim hfixed hSimon hprojection)

set_option linter.style.longLine false in


theorem
    freePosSubcriticalCorrBridge_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale
      hlim hfixed hsimon hstrict hdiag hprofile)

set_option linter.style.longLine false in


theorem
    freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale
      hlim hfixed hfinite hstrict hdiag hprofile)

set_option linter.style.longLine false in


theorem
    freePosSubcriticalCorrBridge_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale
      hlim hfixed hSimon hstrict hdiag hprofile)


theorem freePosSubcriticalCorrBridge_of_finiteIsingSimon_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteIsingSimon_projection
      hlim hfixed hSimon hprojection)


theorem freePosSubcriticalCorrBridge_of_finiteIsingSimon_doubledBoxProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxProjection
      hlim hfixed hSimon hprojection)


theorem freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceProjection
      hlim hfixed hSimon hprojection)


theorem
    freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection
      hlim hfixed hSimon hprojection)


theorem
    freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstep :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep
      hlim hfixed hSimon hstep)


theorem
    freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches
      hlim hfixed hSimon hstrict hdiag)


theorem freePosSubcriticalCorrBridge_of_subexpComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_subexpComparisonToXAxis
      hlim hfixed hcompare)


theorem freePosSubcriticalCorrBridge_of_polynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_polynomialComparisonToXAxis
      hlim hfixed hcompare)


theorem freePosSubcriticalCorrBridge_of_finiteVolumeComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteVolumeComparisonToXAxis
      hlim hfixed hcompare)


theorem freePosSubcriticalCorrBridge_of_finiteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis
      hlim hfixed hcompare)


theorem freePosSubcriticalCorrBridge_of_envelopeAtLeastMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (henv :
      FreeQ2BoundaryVertexEnvelopeAtLeastMassPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_envelopeAtLeastMass hlim hfixed henv)


theorem freePosSubcriticalCorrBridge_of_polynomialAtLeastMass
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hpoly :
      FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_polynomialAtLeastMass
      hlim hfixed hpoly)


theorem freePosSubcriticalCorrBridge_of_polynomialRateWithXAxisLogRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate
      hlim hfixed hrate)


theorem freePosSubcriticalCorrBridge_of_directionalRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_directionalRate hlim hfixed hdir)


theorem freePosSubcriticalCorrBridge_of_convexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper
      hlim hfixed htension)


theorem freePosSubcriticalCorrBridge_of_actualConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper
      hlim hfixed htension)


theorem freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_boundaryPointwise
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryVertexPointwise hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hprofile


theorem freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_subexpComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_subexpComparisonToXAxis hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hcompare


theorem freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_boundaryPointwise
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_boundaryPointwise
      hlim hdecay hprofile)


theorem freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_subexpComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_subexpComparisonToXAxis
      hlim hdecay hcompare)


theorem
    freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hcompare


theorem
    freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)


theorem
    freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_polynomialRateWithXAxisLogRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hrate


theorem freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_directionalRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_directionalRate hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hdir


theorem freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_convexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    htension


theorem
    freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_actualConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    htension


theorem
    freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_polynomialRateWithXAxisLogRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_polynomialRateWithXAxisLogRate
      hlim hdecay hrate)


theorem freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_directionalRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_directionalRate
      hlim hdecay hdir)


theorem freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_convexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_convexSurfaceTensionUpper
      hlim hdecay htension)


theorem
    freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_actualConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_actualConvexSurfaceTensionUpper
      hlim hdecay htension)


theorem freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate
    (h : FreeQ2ProfileSeparatePositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  rcases h β hβpos hβc with
    ⟨hIsing, Alo, AfkHi, AprofHi, Ahi, mass, hmass, hconn,
      hAhiPos, hAhiLog, hProfileHi, hCombine⟩
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate
      hβpos hIsing hconn hAhiPos hAhiLog hProfileHi hCombine⟩


theorem plusPosSubcriticalMassBridge_of_freeQ2ProfileSeparate
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreeQ2ProfileSeparatePositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge :=
  plusPositiveSubcriticalMassBridge_of_free_and_agree hagree
    (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate h)


theorem freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate
    (h : FreeQ2ProfileSeparatePositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate h)


theorem plusPosSubcriticalCorrBridge_of_freeQ2ProfileSeparate
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (h : FreeQ2ProfileSeparatePositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_freeQ2ProfileSeparate hagree h)


theorem freePosSubcriticalMassBridge_of_freeFVQ2Exact
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hA, hmass, hexact⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
      hβpos hA (hcmp β hβpos) hexact⟩


theorem plusPosSubcriticalMassBridge_of_freeFVQ2Exact
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hA, hmass, hexact⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
      hβpos hβc hA hagree (hcmp β hβpos) hexact⟩


theorem freePosSubcriticalMassBridge_of_freeFVQ2Subexp
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hmass, hsubexp⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
      hβpos (hcmp β hβpos) hsubexp⟩


theorem plusPosSubcriticalMassBridge_of_freeFVQ2Subexp
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hmass, hsubexp⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
      hβpos hβc hagree (hcmp β hβpos) hsubexp⟩


theorem freePosSubcriticalMassBridge_of_freeFVQ2TwoSided
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨Alo, Ahi, mass, hmass, hbounds⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
      hβpos (hcmp β hβpos) hbounds⟩


theorem plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨Alo, Ahi, mass, hmass, hbounds⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
      hβpos hβc hagree (hcmp β hβpos) hbounds⟩


theorem freePosSubcriticalMassBridge_of_wiredFVQ2Exact
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2ExactPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hA, hmass, hexact⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
      hβpos hA (hbad β hβpos hβc) (hcmp β hβpos) hexact⟩


theorem plusPosSubcriticalMassBridge_of_wiredFVQ2Exact
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2ExactPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hA, hmass, hexact⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
      hβpos hβc hA hagree (hbad β hβpos hβc)
      (hcmp β hβpos) hexact⟩


theorem freePosSubcriticalMassBridge_of_wiredFVQ2Subexp
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hmass, hsubexp⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
      hβpos (hbad β hβpos hβc) (hcmp β hβpos) hsubexp⟩


theorem plusPosSubcriticalMassBridge_of_wiredFVQ2Subexp
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hmass, hsubexp⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
      hβpos hβc hagree (hbad β hβpos hβc)
      (hcmp β hβpos) hsubexp⟩


theorem freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨Alo, Ahi, mass, hmass, hbounds⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
      hβpos (hbad β hβpos hβc) (hcmp β hβpos) hbounds⟩


theorem plusPosSubcriticalMassBridge_of_wiredFVQ2TwoSided
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨Alo, Ahi, mass, hmass, hbounds⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
      hβpos hβc hagree (hbad β hβpos hβc)
      (hcmp β hβpos) hbounds⟩


theorem freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hA, hmass, hexact⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
      hβpos hA (hcmp β hβpos hβc) hexact⟩


theorem plusPosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hA, hmass, hexact⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_exactExponential
      hβpos hβc hA hagree (hcmp β hβpos hβc) hexact⟩


theorem freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hmass, hsubexp⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
      hβpos (hcmp β hβpos hβc) hsubexp⟩


theorem plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hmass, hsubexp⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_subexponentialPrefactor
      hβpos hβc hagree (hcmp β hβpos hβc) hsubexp⟩


theorem freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨Alo, Ahi, mass, hmass, hbounds⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
      hβpos (hcmp β hβpos hβc) hbounds⟩


theorem plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨Alo, Ahi, mass, hmass, hbounds⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_freeFiniteVolumeQ2_twoSided
      hβpos hβc hagree (hcmp β hβpos hβc) hbounds⟩


theorem freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC
    (freeQ2PositiveSubcriticalComparisonBelowBetaC_of_restrictedCylinderComparison
      hcmp)
    hdecay


theorem plusPosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge :=
  plusPosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC
    hagree
    (freeQ2PositiveSubcriticalComparisonBelowBetaC_of_restrictedCylinderComparison
      hcmp)
    hdecay


theorem freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC
    (freeQ2PositiveSubcriticalComparisonBelowBetaC_of_restrictedCylinderComparison
      hcmp)
    hdecay


theorem plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge :=
  plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC
    hagree
    (freeQ2PositiveSubcriticalComparisonBelowBetaC_of_restrictedCylinderComparison
      hcmp)
    hdecay


theorem freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC
    (freeQ2PositiveSubcriticalComparisonBelowBetaC_of_restrictedCylinderComparison
      hcmp)
    hdecay


theorem plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge :=
  plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC
    hagree
    (freeQ2PositiveSubcriticalComparisonBelowBetaC_of_restrictedCylinderComparison
      hcmp)
    hdecay


theorem freePosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2ExactPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hA, hmass, hexact⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
      hβpos hA (hbad β hβpos hβc) (hcmp β hβpos hβc) hexact⟩


theorem plusPosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2ExactPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hA, hmass, hexact⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_exactExponential
      hβpos hβc hA hagree (hbad β hβpos hβc)
      (hcmp β hβpos hβc) hexact⟩


theorem freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hmass, hsubexp⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
      hβpos (hbad β hβpos hβc) (hcmp β hβpos hβc) hsubexp⟩


theorem plusPosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨A, mass, hmass, hsubexp⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_subexponentialPrefactor
      hβpos hβc hagree (hbad β hβpos hβc)
      (hcmp β hβpos hβc) hsubexp⟩


theorem freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨Alo, Ahi, mass, hmass, hbounds⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    free_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
      hβpos (hbad β hβpos hβc) (hcmp β hβpos hβc) hbounds⟩


theorem plusPosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
    PlusPositiveSubcriticalMassBridge := by
  intro β hβpos hβc
  obtain ⟨Alo, Ahi, mass, hmass, hbounds⟩ := hdecay β hβpos hβc
  exact ⟨mass, hmass,
    plus_hasInverseCorrelationLength_xAxis_of_wiredFiniteVolumeQ2_twoSided
      hβpos hβc hagree (hbad β hβpos hβc)
      (hcmp β hβpos hβc) hbounds⟩


theorem freePosSubcriticalCorrBridge_of_freeFVQ2Exact
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2Exact hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_freeFVQ2Exact
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_freeFVQ2Exact hagree hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_freeFVQ2Subexp
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2Subexp hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_freeFVQ2Subexp hagree hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided hagree hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_wiredFVQ2Exact
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2ExactPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_wiredFVQ2Exact hbad hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_wiredFVQ2Exact
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2ExactPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_wiredFVQ2Exact
      hagree hbad hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp hbad hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_wiredFVQ2Subexp
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_wiredFVQ2Subexp
      hagree hbad hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_wiredFVQ2TwoSided
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparison)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_wiredFVQ2TwoSided
      hagree hbad hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC
      hagree hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC
      hagree hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC
      hagree hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_freeFVQ2Exact_restrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison
      hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_freeFVQ2Exact_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison
      hagree hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
      hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
      hagree hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
      hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
      hagree hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2ExactPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC
      hbad hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2ExactPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC
      hagree hbad hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC
      hbad hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC
      hagree hbad hcmp hdecay)


theorem freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
      hbad hcmp hdecay)


theorem plusPosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbad : Q2PositiveSubcriticalNotBad)
    (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
    (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
    PlusPositiveSubcriticalCorrelationLengthBridge :=
  plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (plusPosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC
      hagree hbad hcmp hdecay)

end Exact3D
end StatMech
