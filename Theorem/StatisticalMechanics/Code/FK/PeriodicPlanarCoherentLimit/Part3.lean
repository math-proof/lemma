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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part2
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

@[simp] theorem PeriodicGraph.bufferedRadius_zero (P : PeriodicGraph V) :
    P.bufferedRadius 0 = 0 := rfl

@[simp] theorem PeriodicGraph.bufferedRadius_succ (P : PeriodicGraph V) (n : ℕ) :
    P.bufferedRadius (n + 1) =
      P.nextBufferedRadius (P.bufferedRadius n) := rfl

theorem PeriodicGraph.bufferedRadius_strictMono (P : PeriodicGraph V) :
    StrictMono P.bufferedRadius := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [P.bufferedRadius_succ]
  exact P.lt_nextBufferedRadius (P.bufferedRadius n)

theorem PeriodicGraph.id_le_bufferedRadius (P : PeriodicGraph V) (n : ℕ) :
    n ≤ P.bufferedRadius n := by
  induction n with
  | zero => simp
  | succ n ih =>
      exact Nat.succ_le_of_lt
        (ih.trans_lt (P.bufferedRadius_strictMono (Nat.lt_succ_self n)))


theorem PeriodicGraph.mem_bufferedBox_of_eventually
    (P : PeriodicGraph V) (v : V) :
    ∃ n, v ∈ P.orbitBox (P.bufferedRadius n) := by
  obtain ⟨n, hn⟩ := P.mem_orbitBox_of_eventually v
  exact ⟨n, P.orbitBox_mono (P.id_le_bufferedRadius n) hn⟩

end PeriodicPlanar
end FK
end StatMech
