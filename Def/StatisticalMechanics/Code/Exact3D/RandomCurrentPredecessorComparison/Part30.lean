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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part31
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def doubledBoxSameBetaResidualEmptyBranchBound
    (β : ℝ) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
  (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
    doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) ≤
      β * edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n)))

set_option linter.style.longLine false in


noncomputable def doubledBoxSameBetaResidualInnerPairBranchBound
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
  (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
    doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) ≤
      β * edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)

set_option linter.style.longLine false in


noncomputable def doubledBoxSameBetaResidualBranchBounds
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
  doubledBoxSameBetaResidualEmptyBranchBound β n v e0 ∧
    doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0

set_option linter.style.longLine false in


noncomputable def doubledBoxSameBetaResidualEmptyBranchSourcePairBound
    (β : ℝ) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
  (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
    doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) ≤
      β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n)))

set_option linter.style.longLine false in


noncomputable def doubledBoxSameBetaResidualInnerPairBranchSourcePairBound
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
  (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
    doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) ≤
      β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)

set_option linter.style.longLine false in


noncomputable def doubledBoxSameBetaResidualBranchSourcePairBounds
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
  doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0 ∧
    doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0

end Exact3D
end StatMech
