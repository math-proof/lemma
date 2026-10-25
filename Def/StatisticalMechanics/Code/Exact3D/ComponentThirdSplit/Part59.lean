/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part56
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipResidualShellShare15.expandedIccOfFourShareTotal
    (n : ℕ)
    (zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ)
    (fourShare : Bool → Bool → Bool → ℕ → ℝ) : ℝ :=
  zero_none +
    two_none +
    two_endpoint +
    two_origin +
    two_ghost +
    two_ghost_endpoint +
    two_ghost_origin +
    (∑ k ∈
      Finset.Icc
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          false false false)
        ((2 * n + 1) ^ 3 - 2),
      fourShare false false false k) +
    (∑ k ∈
      Finset.Icc
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          false false true)
        ((2 * n + 1) ^ 3 - 2),
      fourShare false false true k) +
    (∑ k ∈
      Finset.Icc
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          false true false)
        ((2 * n + 1) ^ 3 - 2),
      fourShare false true false k) +
    (∑ k ∈
      Finset.Icc
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          false true true)
        ((2 * n + 1) ^ 3 - 2),
      fourShare false true true k) +
    (∑ k ∈
      Finset.Icc
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          true false false)
        ((2 * n + 1) ^ 3 - 2),
      fourShare true false false k) +
    (∑ k ∈
      Finset.Icc
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          true false true)
        ((2 * n + 1) ^ 3 - 2),
      fourShare true false true k) +
    (∑ k ∈
      Finset.Icc
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          true true false)
        ((2 * n + 1) ^ 3 - 2),
      fourShare true true false k) +
    (∑ k ∈
      Finset.Icc
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          true true true)
        ((2 * n + 1) ^ 3 - 2),
      fourShare true true true k)

end Exact3D
end StatMech
