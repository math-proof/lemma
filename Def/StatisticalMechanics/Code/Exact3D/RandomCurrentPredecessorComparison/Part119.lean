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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part126
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


def
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in Filter.atTop,
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
                          β n v hvwedge hlt hypos e0 Ω S ew

end Exact3D
end StatMech
