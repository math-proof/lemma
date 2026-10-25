/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeSourceArc
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisOrContactObstruction.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWSourceArcPlacement.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def RlcRelaxedLocalDefectsHitTraceSubwalksOf {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v) : Prop :=
  ∀ {x y : Site 2}
    (a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y),
    (∀ e ∈ a.edges, e ∈ p.edges) →
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 →
    rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 →
    ∃ f g : Site 2, s(f, g) ∈ a.edges ∧
      ¬ rlc_contourEdgeRelaxedLocal G f g


def RlcFaceBoundaryWalkCarriesRelaxedTraceArc {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v) : Prop :=
  ∃ (x y : Site 2)
    (a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y),
    (∀ e ∈ a.edges, e ∈ p.edges) ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
        rlc_contourEdgeRelaxedLocal G f g


end Universality
end StatMech
