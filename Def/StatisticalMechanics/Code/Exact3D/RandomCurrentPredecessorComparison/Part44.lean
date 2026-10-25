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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part45
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def doubledBoxAllComplementWitnessCardWeightFactor
    (β : ℝ) (n : ℕ) (w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) : ℝ :=
  ∑ B : Finset (FK.boxVerts 3 (2 * n)),
    (((edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n w) B
      (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m)

end Exact3D
end StatMech
