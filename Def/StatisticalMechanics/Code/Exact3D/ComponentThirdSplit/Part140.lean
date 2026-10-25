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
import Abbrev.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part8
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget :
    BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget :=
  fun β H n v =>
    (boundaryVertexBoxSimonCurrentRatio β n v / 3) /
      ((β * H) / Real.tanh (β * H))

set_option linter.style.longLine false in


def BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPaymentPositiveSubcritical
    (q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ _Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            ((β * H) / Real.tanh (β * H)) * q β H n v ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPositiveRatioPaymentPositiveSubcritical
    (q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ _Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            q β H n v ≤
              (boundaryVertexBoxSimonCurrentRatio β n v / 3) /
                ((β * H) / Real.tanh (β * H))

end Exact3D
end StatMech
