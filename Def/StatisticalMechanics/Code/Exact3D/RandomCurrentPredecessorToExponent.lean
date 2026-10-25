/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorToExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part184
set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

namespace FiniteCurrentMassBridgeInputs

noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (honeJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_expectationJ
      honeJ)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (honeJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_expectationJ
      honeJ)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (honeJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_expectationJPositiveSubcritical
      honeJ)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (honeJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_expectationJPositiveSubcritical
      honeJ)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_predecessorCasesPositiveSubcritical
      hcases)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_predecessorCasesPositiveSubcritical
      hcases)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical_of_currentSumCasesPositiveSubcritical
      hcases)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical_of_currentSumCasesPositiveSubcritical
      hcases)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_sourcePairCasesPositiveSubcritical
      hcases)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_sourcePairCasesPositiveSubcritical
      hcases)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical_of_edgeCopyCollapsedCasesPositiveSubcritical
      hcases)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical_of_edgeCopyCollapsedCasesPositiveSubcritical
      hcases)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorInjectionRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorInjectionRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorImageRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorImageRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorImageMultiplicityPreservingRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorImageMultiplicityPreservingRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorImageEdgeRelabelRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorImageEdgeRelabelRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale
    hlim hdecay hfinite
    (StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsProfileDoubleScale
    hlim hdecay hSimon
    (StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
      hrows)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal)
    (hdiagYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal_of_expectationJ
      hstrictZJ)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal_of_expectationJ
      hdiagYJ)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal_of_expectationJ
      hstrictYJ)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal)
    (hdiagYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal_of_expectationJ
      hstrictZJ)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal_of_expectationJ
      hdiagYJ)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal_of_expectationJ
      hstrictYJ)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJYLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal_of_expectationJ
      hstrictYJ)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJYLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal_of_expectationJ
      hstrictYJ)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesExpectationJYPositiveSubcritical
      hstrictZ hdiagY hstrictYJ)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesExpectationJYPositiveSubcritical
      hstrictZ hdiagY hstrictYJ)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBranch :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical_of_sourceSectorResidualMomentBranchExpectationJSplitPositiveSubcritical
      hstrictYBranch)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBranch :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorExpectationJYProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical_of_sourceSectorResidualMomentBranchExpectationJSplitPositiveSubcritical
      hstrictYBranch)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYComponent :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitPositiveSubcritical_of_branchComponentExpectationJSplitPositiveSubcritical
      hstrictYComponent)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYComponent :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchExpectationJSplitPositiveSubcritical_of_branchComponentExpectationJSplitPositiveSubcritical
      hstrictYComponent)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitPositiveSubcritical_of_branchComponentBoundsExpectationJSplitPositiveSubcritical
      hstrictYBounds)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitPositiveSubcritical_of_branchComponentBoundsExpectationJSplitPositiveSubcritical
      hstrictYBounds)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitPositiveSubcritical_of_branchComponentBoundsExpectationJRatioGapPositiveSubcritical
      hstrictYBounds)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitPositiveSubcritical_of_branchComponentBoundsExpectationJRatioGapPositiveSubcritical
      hstrictYBounds)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical)
    (hstrictYSplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitPositiveSubcritical_of_branchComponentBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictYBounds hstrictYSplit)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical)
    (hstrictYSplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitPositiveSubcritical_of_branchComponentBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictYBounds hstrictYSplit)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapPositiveSubcritical_of_branchComponentBoundsPositiveSubcritical_expectationJRatioGapPositiveSubcritical
      hstrictYBounds hstrictYRatio)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapPositiveSubcritical_of_branchComponentBoundsPositiveSubcritical_expectationJRatioGapPositiveSubcritical
      hstrictYBounds hstrictYRatio)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_emptyBoundPositiveSubcritical_innerPairBoundPositiveSubcritical
      hempty hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_emptyBoundPositiveSubcritical_innerPairBoundPositiveSubcritical
      hempty hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hselected :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_selectedCopyBoundsPositiveSubcritical
      hselected)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hselected :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_selectedCopyBoundsPositiveSubcritical
      hselected)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical_of_selectedCopyEmptyBoundPositiveSubcritical_selectedCopyInnerPairBoundPositiveSubcritical
      hempty hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical_of_selectedCopyEmptyBoundPositiveSubcritical_selectedCopyInnerPairBoundPositiveSubcritical
      hempty hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundPositiveSubcritical_of_selectedCopyEmptyFiniteCutoffBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundPositiveSubcritical_of_selectedCopyInnerPairFiniteCutoffBoundPositiveSubcritical
      hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundPositiveSubcritical_of_selectedCopyEmptyFiniteCutoffBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundPositiveSubcritical_of_selectedCopyInnerPairFiniteCutoffBoundPositiveSubcritical
      hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffMajorantBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffMajorantBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundPositiveSubcritical_of_selectedCopyEmptyFiniteCutoffMajorantBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundPositiveSubcritical_of_selectedCopyInnerPairFiniteCutoffMajorantBoundPositiveSubcritical
      hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffMajorantBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffMajorantBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundPositiveSubcritical_of_selectedCopyEmptyFiniteCutoffMajorantBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundPositiveSubcritical_of_selectedCopyInnerPairFiniteCutoffMajorantBoundPositiveSubcritical
      hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffMajorantBoundPositiveSubcritical_of_selectedCopyEmptyFiniteCutoffCaseTableBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffMajorantBoundPositiveSubcritical_of_selectedCopyInnerPairFiniteCutoffCaseTableBoundPositiveSubcritical
      hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffMajorantBoundPositiveSubcritical_of_selectedCopyEmptyFiniteCutoffCaseTableBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffMajorantBoundPositiveSubcritical_of_selectedCopyInnerPairFiniteCutoffCaseTableBoundPositiveSubcritical
      hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffExplicitCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffExplicitCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffCaseTableBoundPositiveSubcritical_of_selectedCopyEmptyFiniteCutoffExplicitCaseTableBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffCaseTableBoundPositiveSubcritical_of_selectedCopyInnerPairFiniteCutoffExplicitCaseTableBoundPositiveSubcritical
      hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffExplicitCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffExplicitCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffCaseTableBoundPositiveSubcritical_of_selectedCopyEmptyFiniteCutoffExplicitCaseTableBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffCaseTableBoundPositiveSubcritical_of_selectedCopyInnerPairFiniteCutoffExplicitCaseTableBoundPositiveSubcritical
      hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffExplicitCaseTableBoundPositiveSubcritical_of_selectedCopyEmptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffExplicitCaseTableBoundPositiveSubcritical_of_selectedCopyInnerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical
      hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffExplicitCaseTableBoundPositiveSubcritical_of_selectedCopyEmptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffExplicitCaseTableBoundPositiveSubcritical_of_selectedCopyInnerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical
      hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_emptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical_innerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical
      hempty hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_emptyFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical_innerPairFiniteCutoffRelaxedExplicitCaseTableBoundPositiveSubcritical
      hempty hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_emptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical_innerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical
      hempty hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_emptyFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical_innerPairFiniteCutoffActiveRelaxedExplicitCaseTableBoundPositiveSubcritical
      hempty hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_emptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical_innerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical
      hempty hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffPredicateActiveRelaxedExplicitCaseTableEmptyInnerBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_emptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical_innerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundPositiveSubcritical
      hempty hinner)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_finiteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_finiteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_finiteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsPositiveSubcritical_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsPositiveSubcritical_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsPositiveSubcritical_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsPositiveSubcritical_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsPositiveSubcritical_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsPositiveSubcritical_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAndExpectationJRatioGapProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsPositiveSubcritical)
    (hstrictYRatio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAndExpectationJRatioGapProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsPositiveSubcritical_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsPositiveSubcritical
      htable)
    hstrictYRatio hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYVertexEdge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale
    hlim hdecay hfinite hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitPositiveSubcritical_of_branchComponentVertexEdgeExpectationJSplitPositiveSubcritical
      hstrictYVertexEdge)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYVertexEdge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitProfileDoubleScale
    hlim hdecay hSimon hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentExpectationJSplitPositiveSubcritical_of_branchComponentVertexEdgeExpectationJSplitPositiveSubcritical
      hstrictYVertexEdge)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumBoundsExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictZ hdiagY hempty hinner hJsplit)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumBoundsExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictZ hdiagY hempty hinner hJsplit)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYExactSupportOwnerResidualSourcePairFiniteCellCoverRouteShareBoundsExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictZ hdiagY hcover hJsplit)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYExactSupportOwnerResidualSourcePairFiniteCellCoverRouteShareBoundsExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictZ hdiagY hcover hJsplit)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumMajorantBoundsExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumMajorantBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumMajorantBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumMajorantBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictZ hdiagY hempty hinner hJsplit)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumMajorantBoundsExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumMajorantBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumMajorantBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumMajorantBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictZ hdiagY hempty hinner hJsplit)
    hprofile


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictZ hdiagY hempty hinner hJsplit)
    hprofile


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsExpectationJSplitProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictZ hdiagY hempty hinner hJsplit)
    hprofile


end FiniteCurrentMassBridgeInputs
end Exact3D
end StatMech
