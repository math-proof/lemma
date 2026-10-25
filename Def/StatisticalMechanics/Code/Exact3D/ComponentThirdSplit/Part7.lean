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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part7
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceSourceInactiveSigmaZeroWeightNonzeroBranchPositiveSubcritical :
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
                    (fun a => ¬ finiteBoundaryGhostFullSourceOnePoint n a.1),
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
                  β H n v a) ≤
              0

set_option linter.style.longLine false in

noncomputable def finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) : ℝ :=
  ∑ a ∈
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
        n Ω v).filter
        (fun a => finiteBoundaryGhostFullSourceOnePoint n a.1),
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
        β H n v a

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) : ℝ :=
  ∑ a ∈
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
        n Ω v).filter
        (fun a => ¬ finiteBoundaryGhostFullSourceOnePoint n a.1),
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
        β H n v a

end Exact3D
end StatMech
