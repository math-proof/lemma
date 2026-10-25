/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part5
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

def rlc_stdf_gapRegionCore : Finset (Site 2) :=
  {![-1, -2], ![-1, -1], ![0, -1]}

def rlc_stdf_gapRegionBlockedNeighbors : Finset (Site 2) :=
  {![0, -2], ![-2, -2], ![-2, -1], ![-1, 0], ![1, -1], ![0, 0]}

end Universality
end StatMech
