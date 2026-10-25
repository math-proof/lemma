/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Def.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part5
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem highTempSwitch_mem_outputs (S : Finset V) (o z : V)
    (ho : o ∈ S) (hz : z ∉ S) (p : HighTempSwitchInput (V := V))
    (hp : p ∈ highTempSwitchInputs G S o z) :
    highTempSwitch G S o z ho hz p (by simpa [highTempSwitchInputs] using hp)
      ∈ highTempSwitchOutputs G S o z := by
  classical
  have hpv : p.Valid G S o z := by
    simpa [highTempSwitchInputs] using hp
  let K := p.F ∆ p.H
  let d := highTempFirstExit G K
    (highTempInput_symmDiff_subset G hpv)
    (highTempInput_symmDiff_sources G hpv) S ho hz
  have hQG : d.Q ⊆ G.edgeFinset := d.Q_subset.trans
    (highTempInput_symmDiff_subset G hpv)
  have hQI : d.Q ⊆ highTempInternalEdges G S := by
    intro e he
    exact (mem_highTempInternalEdges G S e).2 ⟨hQG he, d.Q_inside e he⟩
  have hAsub : p.H ∆ d.Q ⊆ highTempInternalEdges G S := by
    intro e he
    rw [Finset.mem_symmDiff] at he
    exact he.elim (fun h => hpv.2.1 h.1) (fun h => hQI h.1)
  have hBsub : (p.F ∆ d.Q).erase s(d.x, d.y) ⊆ G.edgeFinset := by
    intro e he
    have he' := Finset.mem_of_mem_erase he
    rw [Finset.mem_symmDiff] at he'
    exact he'.elim (fun h => hpv.1 h.1) (fun h => hQG h.1)
  have hexitF : s(d.x, d.y) ∈ p.F := by
    have heK := d.exit_mem
    change s(d.x, d.y) ∈ p.F ∆ p.H at heK
    rw [Finset.mem_symmDiff] at heK
    rcases heK with h | h
    · exact h.1
    · exfalso
      have hinside := (mem_highTempInternalEdges G S _).mp (hpv.2.1 h.1) |>.2
      exact d.y_notMem (hinside d.y (Sym2.mem_mk_right d.x d.y))
  have hsources := hasOddBoundary_switch_erase_exit
    hpv.2.2.1 hpv.2.2.2 d.Q_sources d.ne hexitF d.exit_notMem
  rw [highTempSwitchOutputs, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  change HighTempSwitchOutput.Valid G S o z
    (highTempSwitch G S o z ho hz p _) at ⊢
  simpa only [highTempSwitch, K, d] using
    ⟨d.x_mem, d.y_notMem, hAsub, hBsub, hsources.1, hsources.2⟩


theorem highTempSwitch_recover_symmDiff
    (F H Q : Finset (Sym2 V)) {e : Sym2 V}
    (heF : e ∈ F) (heQ : e ∉ Q) :
    insert e ((F ∆ Q).erase e) ∆ (H ∆ Q) = F ∆ H := by
  have he : e ∈ F ∆ Q := by
    exact Finset.mem_symmDiff.mpr (Or.inl ⟨heF, heQ⟩)
  rw [Finset.insert_erase he]
  ext a
  simp only [Finset.mem_symmDiff]
  tauto


theorem highTempSwitch_recover_F
    (F Q : Finset (Sym2 V)) {e : Sym2 V}
    (heF : e ∈ F) (heQ : e ∉ Q) :
    insert e ((F ∆ Q).erase e) ∆ Q = F := by
  have he : e ∈ F ∆ Q := by
    exact Finset.mem_symmDiff.mpr (Or.inl ⟨heF, heQ⟩)
  rw [Finset.insert_erase he]
  ext a
  simp only [Finset.mem_symmDiff]
  tauto


theorem highTempSwitch_recover_H (H Q : Finset (Sym2 V)) :
    (H ∆ Q) ∆ Q = H := by
  ext a
  simp only [Finset.mem_symmDiff]
  tauto


end Sharpness
end StatMech
