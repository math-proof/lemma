/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part8
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

variable [Countable V]


omit [Countable V] in
theorem PeriodicGraph.monotone_bufferedRestrictLE
    (P : PeriodicGraph V) {n m : ℕ} (hnm : n ≤ m) :
    Monotone (P.bufferedRestrictLE hnm) := by
  intro omega eta home e
  exact home _

omit [Countable V] in
theorem PeriodicGraph.edgeIncl_bufferedVertexInclLE
    (P : PeriodicGraph V) {n m : ℕ} (hnm : n ≤ m)
    (e : Sym2 (P.BufferedVertex n)) :
    P.edgeIncl (P.bufferedRadius m)
        (Sym2.map (P.bufferedVertexInclLE hnm) e) =
      P.edgeIncl (P.bufferedRadius n) e := by
  induction e using Sym2.inductionOn with
  | _ x y => rfl

omit [Countable V] in
@[simp] theorem PeriodicGraph.bufferedRestrict_extendEdge_le
    (P : PeriodicGraph V) {n m : ℕ} (hnm : n ≤ m)
    (omega : ConfigSpace (Sym2 (P.BufferedVertex m))) :
    P.bufferedRestrict n (P.extendEdge (P.bufferedRadius m) omega) =
      P.bufferedRestrictLE hnm omega := by
  funext e
  unfold PeriodicGraph.bufferedRestrict PeriodicGraph.bufferedRestrictLE
  rw [← P.edgeIncl_bufferedVertexInclLE hnm e,
    P.extendEdge_edgeIncl]

omit [Countable V] in
theorem PeriodicGraph.bufferedRestrictLE_succ
    (P : PeriodicGraph V) {N m : ℕ} (hNm : N ≤ m)
    (omega : ConfigSpace (Sym2 (P.BufferedVertex (m + 1)))) :
    P.bufferedRestrictLE (hNm.trans (Nat.le_succ m)) omega =
      P.bufferedRestrictLE hNm
        (ocd_innerRestrict (P.bufferedVertexIncl m) omega) := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y => rfl


end PeriodicPlanar
end FK
end StatMech
