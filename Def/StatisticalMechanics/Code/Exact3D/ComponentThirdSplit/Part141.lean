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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part128
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairComparisonPositiveSubcritical
    (q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ _Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let G := Sharpness.withGhost (FK.boxGraph 3 n)
            let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H
              (fun _ => 1)
            let A : Finset (Option (FK.boxVerts 3 n)) :=
              ({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
            edgeCopySourcePairEmptyCollapsedSum G β J A ≤
              q β H n v *
                edgeCopySourcePairEmptyCollapsedSum G β J
                  (∅ : Finset (Option (FK.boxVerts 3 n)))

set_option linter.style.longLine false in


def BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
    (q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ _Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let G := Sharpness.withGhost (FK.boxGraph 3 n)
            let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H
              (fun _ => 1)
            let A : Finset (Option (FK.boxVerts 3 n)) :=
              ({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
            edgeCopySourcePairEmptyCollapsedSum G β J A /
                edgeCopySourcePairEmptyCollapsedSum G β J
                  (∅ : Finset (Option (FK.boxVerts 3 n))) ≤
              q β H n v

end Exact3D
end StatMech
