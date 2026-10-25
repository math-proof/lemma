/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Def.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part4
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

@[simp]
theorem rlc_scaleTwoDoubleFailureConfig_eq_true_iff
    (e : Sym2 (Site 2)) :
    rlc_scaleTwoDoubleFailureConfig e = true ↔
      e ∈ rlc_scaleTwoDoubleFailureOpenEdges := by
  simp [rlc_scaleTwoDoubleFailureConfig]

end Universality
end StatMech
