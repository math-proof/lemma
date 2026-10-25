/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicPlaneEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part8
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicPlaneEmbedding
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triangularStraightEdgeArc_disjoint_of_intersection
    (hinter : TriangularStraightEdgeIntersectionProperty)
    {x y z w : Site 2}
    (hxy : triangularGraph.Adj x y) (hzw : triangularGraph.Adj z w)
    (hxz : Ne x z) (hxw : Ne x w) (hyz : Ne y z) (hyw : Ne y w) :
    Disjoint (Set.range (triangularStraightEdgeArc hxy))
      (Set.range (triangularStraightEdgeArc hzw)) := by
  rw [Set.disjoint_left]
  intro p hp hp'
  have hedge : Ne s(x, y) s(z, w) := by
    intro he
    rw [Sym2.eq_iff] at he
    rcases he with h | h
    · exact hxz h.1
    · exact hxw h.1
  obtain ⟨v, hvxy, hvzw, _hv⟩ := hinter hxy hzw p hedge hp hp'
  rcases hvxy with rfl | rfl
  · rcases hvzw with rfl | rfl
    · exact hxz rfl
    · exact hxw rfl
  · rcases hvzw with rfl | rfl
    · exact hyz rfl
    · exact hyw rfl

theorem hexagonalStraightEdgeArc_disjoint_of_intersection
    (hinter : HexagonalStraightEdgeIntersectionProperty)
    {x y z w : HexVertex}
    (hxy : hexagonalGraph.Adj x y) (hzw : hexagonalGraph.Adj z w)
    (hxz : Ne x z) (hxw : Ne x w) (hyz : Ne y z) (hyw : Ne y w) :
    Disjoint (Set.range (hexagonalStraightEdgeArc hxy))
      (Set.range (hexagonalStraightEdgeArc hzw)) := by
  rw [Set.disjoint_left]
  intro p hp hp'
  have hedge : Ne s(x, y) s(z, w) := by
    intro he
    rw [Sym2.eq_iff] at he
    rcases he with h | h
    · exact hxz h.1
    · exact hxw h.1
  obtain ⟨v, hvxy, hvzw, _hv⟩ := hinter hxy hzw p hedge hp hp'
  rcases hvxy with rfl | rfl
  · rcases hvzw with rfl | rfl
    · exact hxz rfl
    · exact hxw rfl
  · rcases hvzw with rfl | rfl
    · exact hyz rfl
    · exact hyw rfl


end StatMech.FK.PeriodicPlanar
