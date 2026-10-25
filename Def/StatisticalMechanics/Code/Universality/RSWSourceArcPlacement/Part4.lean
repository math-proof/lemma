/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeSourceArc
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisOrContactObstruction.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWSourceArcPlacement.Part4
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def rlc_traceSplitCounterexample_boundaryArc
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Walk
        ![-1, -2] ![1, -1] :=
  .cons (rlc_traceSplitCounterexample_boundary_adj₀₁ omega hK)
    (.cons (rlc_traceSplitCounterexample_boundary_adj₁₂ omega hK)
      (.cons (rlc_traceSplitCounterexample_boundary_adj₂₃ omega hK) .nil))

end Universality
end StatMech
