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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part59
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def doubledBoxCompatibleEdgeRelabelIso
    {n : ℕ}
    (φ : FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hends : ∀ e, (σ e).1 = Sym2.map φ e.1) :
    (FK.boxGraph 3 (2 * n)) ≃g (FK.boxGraph 3 (2 * n)) where
  toEquiv := φ
  map_rel_iff' := by
    intro a b
    exact doubledBoxCompatibleEdgeRelabel_adj_iff φ σ hends a b

end Exact3D
end StatMech
