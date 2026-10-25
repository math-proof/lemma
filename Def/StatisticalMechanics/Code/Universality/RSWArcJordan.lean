/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcJordan.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWOuterArc
import Theorem.StatisticalMechanics.Code.Universality.RSWTraceContact.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWArcJordan
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def RlcContourArcLocalSide {n : ℤ}
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
      rlc_reflectedTargetLocallySupported G
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
        rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g)) ∨
    (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_complementaryContourArc c hx hy).edges →
      rlc_reflectedTargetLocallySupported G
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
        rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g))


end Universality
end StatMech
