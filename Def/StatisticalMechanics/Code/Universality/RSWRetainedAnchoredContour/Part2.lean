/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWFailureSelectedCarryObstruction
import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def rlc_traceSplitCounterexample_fullBoundaryCycle :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Walk
        ![-1, -2] ![-1, -2] :=
  .cons rlc_traceSplitCounterexample_fullBoundary_adj01
    (.cons rlc_traceSplitCounterexample_fullBoundary_adj12
      (.cons rlc_traceSplitCounterexample_fullBoundary_adj23
        (.cons rlc_traceSplitCounterexample_fullBoundary_adj34
          (.cons rlc_traceSplitCounterexample_fullBoundary_adj45
            (.cons rlc_traceSplitCounterexample_fullBoundary_adj56
              (.cons rlc_traceSplitCounterexample_fullBoundary_adj67
                (.cons rlc_traceSplitCounterexample_fullBoundary_adj78
                  (.cons rlc_traceSplitCounterexample_fullBoundary_adj89
                    (.cons rlc_traceSplitCounterexample_fullBoundary_adj90
                      .nil)))))))))

end Universality
end StatMech
