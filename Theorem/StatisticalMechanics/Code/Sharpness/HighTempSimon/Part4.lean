/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Def.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part6
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem highTempSwitchMap_injective (S : Finset V) (o z : V)
    (ho : o ∈ S) (hz : z ∉ S) :
    Function.Injective (highTempSwitchMap G S o z ho hz) := by
  classical
  intro p q hpq
  have hpv : p.1.Valid G S o z := by
    have h := p.2
    change p.1 ∈ Finset.univ.filter
      (HighTempSwitchInput.Valid G S o z) at h
    exact (Finset.mem_filter.mp h).2
  have hqv : q.1.Valid G S o z := by
    have h := q.2
    change q.1 ∈ Finset.univ.filter
      (HighTempSwitchInput.Valid G S o z) at h
    exact (Finset.mem_filter.mp h).2
  let dp := highTempFirstExit G (p.1.F ∆ p.1.H)
    (highTempInput_symmDiff_subset G hpv)
    (highTempInput_symmDiff_sources G hpv) S ho hz
  let dq := highTempFirstExit G (q.1.F ∆ q.1.H)
    (highTempInput_symmDiff_subset G hqv)
    (highTempInput_symmDiff_sources G hqv) S ho hz
  have hout :
      highTempSwitch G S o z ho hz p.1 hpv =
        highTempSwitch G S o z ho hz q.1 hqv := by
    exact Subtype.ext_iff.mp hpq
  have hx : dp.x = dq.x := by
    have := congrArg HighTempSwitchOutput.x hout
    simpa only [highTempSwitch, dp, dq] using this
  have hy : dp.y = dq.y := by
    have := congrArg HighTempSwitchOutput.y hout
    simpa only [highTempSwitch, dp, dq] using this
  have hA : p.1.H ∆ dp.Q = q.1.H ∆ dq.Q := by
    have := congrArg HighTempSwitchOutput.A hout
    simpa only [highTempSwitch, dp, dq] using this
  have hB : (p.1.F ∆ dp.Q).erase s(dp.x, dp.y) =
      (q.1.F ∆ dq.Q).erase s(dq.x, dq.y) := by
    have := congrArg HighTempSwitchOutput.B hout
    simpa only [highTempSwitch, dp, dq] using this
  have hB' : (p.1.F ∆ dp.Q).erase s(dq.x, dq.y) =
      (q.1.F ∆ dq.Q).erase s(dq.x, dq.y) := by
    simpa only [hx, hy] using hB
  have hexitFp : s(dp.x, dp.y) ∈ p.1.F := by
    have heK := dp.exit_mem
    change s(dp.x, dp.y) ∈ p.1.F ∆ p.1.H at heK
    rw [Finset.mem_symmDiff] at heK
    rcases heK with h | h
    · exact h.1
    · exfalso
      have hinside := (mem_highTempInternalEdges G S _).mp (hpv.2.1 h.1) |>.2
      exact dp.y_notMem (hinside dp.y (Sym2.mem_mk_right dp.x dp.y))
  have hexitFq : s(dq.x, dq.y) ∈ q.1.F := by
    have heK := dq.exit_mem
    change s(dq.x, dq.y) ∈ q.1.F ∆ q.1.H at heK
    rw [Finset.mem_symmDiff] at heK
    rcases heK with h | h
    · exact h.1
    · exfalso
      have hinside := (mem_highTempInternalEdges G S _).mp (hqv.2.1 h.1) |>.2
      exact dq.y_notMem (hinside dq.y (Sym2.mem_mk_right dq.x dq.y))
  have hK : p.1.F ∆ p.1.H = q.1.F ∆ q.1.H := by
    rw [← highTempSwitch_recover_symmDiff p.1.F p.1.H dp.Q
        hexitFp dp.exit_notMem,
      ← highTempSwitch_recover_symmDiff q.1.F q.1.H dq.Q
        hexitFq dq.exit_notMem]
    rw [hx, hy, hA, hB']
  have hQ : dp.Q = dq.Q := by
    exact highTempFirstExit_Q_congr G hK
      (highTempInput_symmDiff_subset G hpv)
      (highTempInput_symmDiff_subset G hqv)
      (highTempInput_symmDiff_sources G hpv)
      (highTempInput_symmDiff_sources G hqv) S ho hz
  have hH : p.1.H = q.1.H := by
    calc
      p.1.H = (p.1.H ∆ dp.Q) ∆ dp.Q :=
        (highTempSwitch_recover_H p.1.H dp.Q).symm
      _ = (q.1.H ∆ dq.Q) ∆ dq.Q := by rw [hA, hQ]
      _ = q.1.H := highTempSwitch_recover_H q.1.H dq.Q
  have hF : p.1.F = q.1.F := by
    calc
      p.1.F = insert s(dp.x, dp.y)
          ((p.1.F ∆ dp.Q).erase s(dp.x, dp.y)) ∆ dp.Q :=
        (highTempSwitch_recover_F p.1.F dp.Q hexitFp dp.exit_notMem).symm
      _ = insert s(dq.x, dq.y)
          ((q.1.F ∆ dq.Q).erase s(dq.x, dq.y)) ∆ dq.Q := by
        rw [hx, hy, hB', hQ]
      _ = q.1.F :=
        highTempSwitch_recover_F q.1.F dq.Q hexitFq dq.exit_notMem
  apply Subtype.ext
  exact congrArg₂ (fun F H => HighTempSwitchInput.mk F H) hF hH


end Sharpness
end StatMech
