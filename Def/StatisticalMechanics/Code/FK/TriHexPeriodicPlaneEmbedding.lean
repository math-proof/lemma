/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicPlaneEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part8
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def TriangularStraightEdgeIntersectionProperty : Prop :=
  forall {x y z w : Site 2}
    (hxy : triangularGraph.Adj x y) (hzw : triangularGraph.Adj z w)
    (p : Complex),
    Ne s(x, y) s(z, w) ->
    p ∈ Set.range (triangularStraightEdgeArc hxy) ->
    p ∈ Set.range (triangularStraightEdgeArc hzw) ->
      ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) ∧
        triangularPlaneVertex v = p


def HexagonalStraightEdgeIntersectionProperty : Prop :=
  forall {x y z w : HexVertex}
    (hxy : hexagonalGraph.Adj x y) (hzw : hexagonalGraph.Adj z w)
    (p : Complex),
    Ne s(x, y) s(z, w) ->
    p ∈ Set.range (hexagonalStraightEdgeArc hxy) ->
    p ∈ Set.range (hexagonalStraightEdgeArc hzw) ->
      ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) ∧
        hexagonalPlaneVertex v = p

end StatMech.FK.PeriodicPlanar
