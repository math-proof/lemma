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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part26
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (_hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)) :
    { e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset //
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) ∧
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ∧
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w ∧
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w } := by
  let e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset :=
    ⟨s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w), by
        rw [SimpleGraph.mem_edgeFinset]
        exact hadj.symm⟩
  refine ⟨e0, rfl, ?_, ?_, ?_⟩
  · intro h
    have hvzero :
        boxVertTransverseHeight3 v = 0 :=
      boxVertTransverseHeight3_eq_zero_of_doubled_origin_eq_incl h
    omega
  · intro h
    have hw0coord : ((w : Lattice.Site 3) 0).natAbs = 0 := by
      have hsite :
          (Percolation.origin 3 : Lattice.Site 3) = (w : Lattice.Site 3) := by
        simpa [IsingFK.boxOrigin, FK.boxVertInclLE] using
          congrArg Subtype.val h
      have h0 := congrFun hsite (0 : Fin 3)
      simp [Percolation.origin] at h0 ⊢
      simp [← h0]
    have hn0 : n = 0 := by
      have hwx : ((w : Lattice.Site 3) 0) = (n : ℤ) := hwwedge.1
      have : ((n : ℤ).natAbs) = 0 := by
        rw [← hwx]
        exact hw0coord
      omega
    subst n
    have hvzero : boxVertTransverseHeight3 v = 0 :=
      boxVertTransverseHeight3_eq_zero_of_radius_zero
    omega
  · intro h
    exact
      (FK.boxGraph 3 (2 * n)).loopless.irrefl
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (by simpa [h] using hadj.symm)

end Exact3D
end StatMech
