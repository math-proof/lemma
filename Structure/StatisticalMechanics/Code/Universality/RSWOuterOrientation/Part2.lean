/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcBadPlacement.Part6
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWOuterOrientation.Part3
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


structure RlcOuterContourContactOrder {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) where
  rightContact : Site 2
  leftContact : Site 2
  right_mem : rightContact ∈ (mpl_orbitFaceLoop
    (rlc_mixedWiredReachSet G omega) (rlc_outerExitAnchor G omega)).support
  left_mem : leftContact ∈ (mpl_orbitFaceLoop
    (rlc_mixedWiredReachSet G omega) (rlc_outerExitAnchor G omega)).support
  right_trace : rlc_dualReflect rightContact ∈
    rlc_pathVertices gamma.1
  left_trace : rlc_dualReflect leftContact ∈
    rlc_pathVertices gamma'.1
  supportedSide :
    (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_orderedContourArc
        (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
          (rlc_outerExitAnchor G omega)) right_mem left_mem).edges →
      rlc_contourEdgeRelaxedLocal G f g) ∨
    (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_complementaryContourArc
        (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
          (rlc_outerExitAnchor G omega)) right_mem left_mem).edges →
      rlc_contourEdgeRelaxedLocal G f g)


end Universality
end StatMech
