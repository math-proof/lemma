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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part6
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceSourceActiveSigmaProfileWeightNonzeroBranchPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            (∑ a ∈
                (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
                  n Ωnz v).filter
                    (fun a => finiteBoundaryGhostFullSourceOnePoint n a.1),
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
                  β H n v a) ≤
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                β H n Ωnz v

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceSourceActiveCurrentProfileWeightNonzeroBranchPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
                β H n
                (Ωnz.filter
                  (fun m => finiteBoundaryGhostFullSourceOnePoint n m)) v ≤
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                β H n Ωnz v

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceSourceActiveCollapsedVertexImageProfileWeightNonzeroBranchPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            (∑ d ∈
                (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex
                  Ωnz v).image,
                (((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex
                    Ωnz v).fiber d).card : ℝ) *
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                β H n Ωnz v

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceSourceActiveCollapsedVertexTargetMultiplicityMainEmptyWeightNonzeroBranchPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            (∑ d ∈ I.image,
                (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
                  ℕ) : ℝ) *
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) ≤
              (I.image.card : ℝ) *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v

end Exact3D
end StatMech
