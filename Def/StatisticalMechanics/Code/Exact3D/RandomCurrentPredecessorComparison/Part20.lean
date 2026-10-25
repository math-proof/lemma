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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part20
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex
    {n : ℕ} {w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    FinsetFiberIndex (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) where
  α := {p // p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
    (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n w) m e0}
  domain := (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
    (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n w) m e0).attach
  map := fun p => Function.update m p.1.2.1 (m p.1.2.1 - 1)

set_option linter.style.longLine false in


noncomputable def doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex
    {n : ℕ} {w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    FinsetFiberIndex (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) where
  α := {p // p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
    (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n w) m e0}
  domain := (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
    (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n w) m e0).attach
  map := fun p => Function.update m p.1.2.1 (m p.1.2.1 - 1)

end Exact3D
end StatMech
