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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part40
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def DoubledBoxOriginIncidentSupportPatternProfileRouteChecks
    (β c : ℝ) (n : ℕ)
    (Ωactive :
      Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (F : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ)
    (profileRoute :
      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
  Set.InjOn (profileRoute S)
      (Ωactive.filter (fun m => doubledBoxOriginIncidentSupport n m = S)) ∧
    (∀ m ∈ Ωactive.filter
        (fun m => doubledBoxOriginIncidentSupport n m = S),
      doubledBoxOriginIncidentSupport n (profileRoute S m) = S) ∧
      ∀ m ∈ Ωactive.filter
          (fun m => doubledBoxOriginIncidentSupport n m = S),
        F m ≤
          c * Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
              (profileRoute S m))

end Exact3D
end StatMech
