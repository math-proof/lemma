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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part37
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def doubledBoxSelectedEdgeCopiesSingletonCutoff
    (n : ℕ) (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) (k : ℕ) :
    Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :=
  {Function.update
    (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k}

set_option linter.style.longLine false in


def doubledBoxOriginTouchesEdgeSupport
    (n : ℕ)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) : Prop :=
  ∃ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
    m e ≠ 0 ∧ IsingFK.boxOrigin 3 (2 * n) ∈ e.1

set_option linter.style.longLine false in


noncomputable def doubledBoxOriginIncidentEdges
    (n : ℕ) :
    Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset) := by
  classical
  exact
    (Finset.univ : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset)).filter
      (fun e => IsingFK.boxOrigin 3 (2 * n) ∈ e.1)

end Exact3D
end StatMech
