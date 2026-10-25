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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part42
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def edgeCopySourcePairDataOriginIncidentOwnerTag
    {n : ℕ} {A B : Finset (FK.boxVerts 3 (2 * n))}
    (fallback : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (d : edgeCopySourcePairData (FK.boxGraph 3 (2 * n)) A B) :
    ↥(FK.boxGraph 3 (2 * n)).edgeFinset :=
  (doubledBoxOriginIncidentOwner n d.1).getD fallback

end Exact3D
end StatMech
