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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem boundaryCrossingCapPairCountMultiplicityBound_summand_nonneg
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    0 ≤
      (∑ w ∈ Finset.univ.filter (fun w : FK.boxVerts 3 n =>
          FK.boxBoundary 3 n w),
        (finiteBoundaryGhostBoundaryCrossingPairCount m w : ℝ)) *
        finiteBoundaryGhostBoundaryGhostMultiplicitySum n m := by
  exact
    mul_nonneg
      (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
      (finiteBoundaryGhostBoundaryGhostMultiplicitySum_nonneg (n := n) m)

set_option linter.style.longLine false in


theorem boundaryCrossingCapPairCountMultiplicityBound_mono
    (β H : ℝ) {n : ℕ}
    {Ω Ω' : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    (hΩ : Ω ⊆ Ω') :
    boundaryCrossingCapPairCountMultiplicityBound β H n Ω ≤
      boundaryCrossingCapPairCountMultiplicityBound β H n Ω' := by
  classical
  unfold boundaryCrossingCapPairCountMultiplicityBound
  unfold finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hΩ
      (fun m _hm _hnot =>
        boundaryCrossingCapPairCountMultiplicityBound_summand_nonneg
          (n := n) m)

end Exact3D
end StatMech
