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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part56
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxCompatibleEdgeRelabel_origin_edist_eq
    {n : ℕ}
    (φ : FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hends : ∀ e, (σ e).1 = Sym2.map φ e.1)
    (horigin :
      φ (IsingFK.boxOrigin 3 (2 * n)) =
        IsingFK.boxOrigin 3 (2 * n))
    (x : FK.boxVerts 3 (2 * n)) :
    (FK.boxGraph 3 (2 * n)).edist
        (IsingFK.boxOrigin 3 (2 * n)) (φ x) =
      (FK.boxGraph 3 (2 * n)).edist
        (IsingFK.boxOrigin 3 (2 * n)) x := by
  have h :=
    simpleGraphIso_edist_eq
      (doubledBoxCompatibleEdgeRelabelIso φ σ hends)
      (IsingFK.boxOrigin 3 (2 * n)) x
  simpa [doubledBoxCompatibleEdgeRelabelIso, horigin] using h

end Exact3D
end StatMech
