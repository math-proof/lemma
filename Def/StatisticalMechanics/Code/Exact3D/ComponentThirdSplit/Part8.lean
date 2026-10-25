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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part8
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) : ℝ :=
  let I :=
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
      (Ω.filter (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m)) v
  ∑ D ∈ I.image,
    (((D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) +
        1 : ℕ) : ℝ) *
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H D)

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) : ℝ :=
  let I :=
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
      (Ω.filter (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m)) v
  ∑ D ∈ I.image.filter
      (fun D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v =>
        D.1 ≠
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v})),
    (((D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) +
        1 : ℕ) : ℝ) *
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H D)

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    Finset (finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v) :=
  let I :=
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
      (Ω.filter (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m)) v
  I.image.filter
    (fun D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v =>
      D.1 ≠
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
    (β H : ℝ) {n : ℕ} {v : FK.boxVerts 3 n}
    (D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v) :
    ℝ :=
  (((D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) : ℝ) *
    finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H D)

end Exact3D
end StatMech
