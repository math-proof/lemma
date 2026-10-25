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
import Abbrev.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def doubledBoxSwitchedSourceSectorResidualMomentBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) : ℝ :=
  (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
    doubledBoxResidualMomentBranchSummand β n v w e0 m

set_option linter.style.longLine false in

noncomputable def doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
    (β : ℝ) (n : ℕ) (v _w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) : ℝ :=
  (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
    doubledBoxResidualMomentEmptyBranchSummand β n v e0 m

set_option linter.style.longLine false in

noncomputable def doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) : ℝ :=
  (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
    doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m

end Exact3D
end StatMech
