/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcJordanCyclic
import Theorem.StatisticalMechanics.Code.Universality.RSWArcBadPlacement.Part4
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def RlcContourArcRelaxedLocalSide {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) : Prop :=
  (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges →
      rlc_contourEdgeRelaxedLocal G f g) ∨
    (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_complementaryContourArc c hx hy).edges →
      rlc_contourEdgeRelaxedLocal G f g)


def RlcContourRelaxedBadEdgesOnOneArcAt {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) : Prop :=
  (∀ {f g : Site 2},
      s(f, g) ∈ c.edges → ¬ rlc_contourEdgeRelaxedLocal G f g →
      s(f, g) ∈ (rlc_complementaryContourArc c hx hy).edges) ∨
    (∀ {f g : Site 2},
      s(f, g) ∈ c.edges → ¬ rlc_contourEdgeRelaxedLocal G f g →
      s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges)


end Universality
end StatMech
