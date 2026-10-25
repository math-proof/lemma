/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicPlaneEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part8
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicPlaneEmbedding
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


noncomputable def triangularPeriodicPlaneEmbedding_of_intersection
    (hinter : TriangularStraightEdgeIntersectionProperty) :
    PeriodicPlaneEmbedding triangular where
  vertex := triangularPlaneVertex
  period := triHexPlanePeriod
  period_injective := triHexPlanePeriod_injective
  coordinates := triHexPlaneCoordinates
  coordinates_period := triHexPlaneCoordinates_period
  vertex_shift := triangularPlaneVertex_shift
  proper := triangularPlaneVertex_bounded_finite
  edgeArc := triangularStraightEdgeArc
  edgeArc_injective := triangularStraightEdgeArc_injective
  edgeArc_symm := triangularStraightEdgeArc_symm
  edgeArc_shift := triangularStraightEdgeArc_shift
  edgeArc_intersection := hinter
  edgeArc_disjoint :=
    triangularStraightEdgeArc_disjoint_of_intersection hinter
  edgeArc_locallyFinite := triangularStraightEdgeArc_locallyFinite


noncomputable def hexagonalPeriodicPlaneEmbedding_of_intersection
    (hinter : HexagonalStraightEdgeIntersectionProperty) :
    PeriodicPlaneEmbedding hexagonal where
  vertex := hexagonalPlaneVertex
  period := triHexPlanePeriod
  period_injective := triHexPlanePeriod_injective
  coordinates := triHexPlaneCoordinates
  coordinates_period := triHexPlaneCoordinates_period
  vertex_shift := hexagonalPlaneVertex_shift
  proper := hexagonalPlaneVertex_bounded_finite
  edgeArc := hexagonalStraightEdgeArc
  edgeArc_injective := hexagonalStraightEdgeArc_injective
  edgeArc_symm := hexagonalStraightEdgeArc_symm
  edgeArc_shift := hexagonalStraightEdgeArc_shift
  edgeArc_intersection := hinter
  edgeArc_disjoint :=
    hexagonalStraightEdgeArc_disjoint_of_intersection hinter
  edgeArc_locallyFinite := hexagonalStraightEdgeArc_locallyFinite

end StatMech.FK.PeriodicPlanar
