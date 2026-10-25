/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Def.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part7
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem highTempSwitch_weight_eq (t : Sym2 V → ℝ)
    (S : Finset V) (o z : V) (ho : o ∈ S) (hz : z ∉ S)
    (p : HighTempSwitchInput (V := V)) (hp : p.Valid G S o z) :
    highTempSwitchOutputWeight t (highTempSwitch G S o z ho hz p hp) =
      highTempSwitchInputWeight t p := by
  let K := p.F ∆ p.H
  let d := highTempFirstExit G K
    (highTempInput_symmDiff_subset G hp)
    (highTempInput_symmDiff_sources G hp) S ho hz
  have hexitF : s(d.x, d.y) ∈ p.F := by
    have heK := d.exit_mem
    change s(d.x, d.y) ∈ p.F ∆ p.H at heK
    rw [Finset.mem_symmDiff] at heK
    rcases heK with h | h
    · exact h.1
    · exfalso
      have hinside := (mem_highTempInternalEdges G S _).mp (hp.2.1 h.1) |>.2
      exact d.y_notMem (hinside d.y (Sym2.mem_mk_right d.x d.y))
  simpa only [highTempSwitchOutputWeight, highTempSwitchInputWeight,
    highTempSwitch, K, d] using
    prod_switch_erase_exit t p.F p.H d.Q d.Q_subset hexitF d.exit_notMem


theorem highTempSwitch_sum_le (t : Sym2 V → ℝ) (ht : ∀ e, 0 ≤ t e)
    (S : Finset V) (o z : V) (ho : o ∈ S) (hz : z ∉ S) :
    (∑ p : ↥(highTempSwitchInputs G S o z),
        highTempSwitchInputWeight t p.1) ≤
      ∑ r : ↥(highTempSwitchOutputs G S o z),
        highTempSwitchOutputWeight t r.1 := by
  classical
  let f := highTempSwitchMap G S o z ho hz
  have hf : Function.Injective f := highTempSwitchMap_injective G S o z ho hz
  have hweight : ∀ p : ↥(highTempSwitchInputs G S o z),
      highTempSwitchInputWeight t p.1 = highTempSwitchOutputWeight t (f p).1 := by
    intro p
    have hpv : p.1.Valid G S o z := by
      have h := p.2
      change p.1 ∈ Finset.univ.filter
        (HighTempSwitchInput.Valid G S o z) at h
      exact (Finset.mem_filter.mp h).2
    exact (highTempSwitch_weight_eq G t S o z ho hz p.1 hpv).symm
  calc
    (∑ p : ↥(highTempSwitchInputs G S o z),
        highTempSwitchInputWeight t p.1) =
        ∑ p : ↥(highTempSwitchInputs G S o z),
          highTempSwitchOutputWeight t (f p).1 := by
            apply Finset.sum_congr rfl
            intro p _
            exact hweight p
    _ = ∑ r ∈ (Finset.univ.image f), highTempSwitchOutputWeight t r.1 := by
      symm
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact hf hab
    _ ≤ ∑ r : ↥(highTempSwitchOutputs G S o z),
        highTempSwitchOutputWeight t r.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro r _ _
      unfold highTempSwitchOutputWeight
      exact mul_nonneg
        (mul_nonneg
          (Finset.prod_nonneg (fun e _ => ht e))
          (ht s(r.1.x, r.1.y)))
        (Finset.prod_nonneg (fun e _ => ht e))


end Sharpness
end StatMech
