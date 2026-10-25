/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWExtremalSelectionObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


noncomputable def rlc_extremalSelectionCounterexampleConfig :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => e ∈
    rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
      rlc_pathEdges rlc_traceSplitCounterexampleLeft.1


end Universality
end StatMech
