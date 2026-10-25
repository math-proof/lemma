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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part60
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def doubledBoxEndpointMapObstruction
    (n : ℕ) (v w : FK.boxVerts 3 n) : Prop :=
  ∀ (φ : FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset),
      (∀ e, (σ e).1 = Sym2.map φ e.1) →
      φ (IsingFK.boxOrigin 3 (2 * n)) =
        IsingFK.boxOrigin 3 (2 * n) →
      φ (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) =
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w →
      False

set_option linter.style.longLine false in


noncomputable def siteParity3 (x : Lattice.Site 3) : ZMod 2 :=
  ∑ i, (x i : ZMod 2)

end Exact3D
end StatMech
