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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

noncomputable def doubledBoxOriginToInnerEndpointSource
    (n : ℕ) (v : FK.boxVerts 3 n) :
    Finset (FK.boxVerts 3 (2 * n)) :=
  ({IsingFK.boxOrigin 3 (2 * n)} : Finset (FK.boxVerts 3 (2 * n))) ∆
    {FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v}


end Exact3D
end StatMech
