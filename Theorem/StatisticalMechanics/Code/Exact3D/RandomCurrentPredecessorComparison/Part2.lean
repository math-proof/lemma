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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem doubledBoxOriginToInnerEndpointSource_eq_pair
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    doubledBoxOriginToInnerEndpointSource n v =
      ({IsingFK.boxOrigin 3 (2 * n),
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v} :
        Finset (FK.boxVerts 3 (2 * n))) := by
  simpa [doubledBoxOriginToInnerEndpointSource] using
    finset_singleton_symmDiff_singleton_eq_pair hov


theorem doubledBoxOriginToInnerEndpointSource_ne_of_endpoint_ne
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    doubledBoxOriginToInnerEndpointSource n v ≠
      doubledBoxOriginToInnerEndpointSource n w := by
  classical
  intro hsrc
  have hmem :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ∈
        doubledBoxOriginToInnerEndpointSource n v := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simp
  have hnot :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ∉
        doubledBoxOriginToInnerEndpointSource n w := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair how]
    simp [hov.symm, hvw]
  exact hnot (by simpa [hsrc] using hmem)


end Exact3D
end StatMech
