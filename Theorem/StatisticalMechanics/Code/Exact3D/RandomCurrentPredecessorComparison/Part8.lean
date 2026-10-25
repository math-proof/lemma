/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part7
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem edgeCopySourcePairEmptyCollapsedMultiplicity_eq_card_of_fullSource
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A) :
    edgeCopySourcePairEmptyCollapsedMultiplicity G A m =
      ((edgeCopySourceSector G A m).card : ℝ) := by
  simp [edgeCopySourcePairEmptyCollapsedMultiplicity, hsrc]


theorem edgeCopySourcePairEmptyCollapsedMultiplicity_eq_zero_of_not_fullSource
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) ≠ A) :
    edgeCopySourcePairEmptyCollapsedMultiplicity G A m = 0 := by
  simp [edgeCopySourcePairEmptyCollapsedMultiplicity, hsrc]


end Exact3D
end StatMech
