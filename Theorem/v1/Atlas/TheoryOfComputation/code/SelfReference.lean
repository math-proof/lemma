/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part13
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Decidability
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Set
import Def.v1.Atlas.TheoryOfComputation.code.SelfReference.Part4


namespace TuringMachine

open TuringMachine

set_option maxHeartbeats 3200000 in
set_option linter.unusedSectionVars false in
/-- Key loop invariant of `printTM`: after `k ≤ |w|` steps on any `input`, the
machine is in state `k`, the head is at position `k`, and tape cells
`0, …, k-1` already hold the first `k` symbols of `w`. Proved by induction on
`k`. -/
theorem printTM_invariant_any_input (blank : Γ) (inputAlpha : Set Γ)
    (h_blank : blank ∉ inputAlpha) (w : List Γ) (input : List Γ)
    (k : ℕ) (hk : k ≤ w.length) :
    ((printTM blank inputAlpha h_blank w).runOnInput input k).state = ⟨k, by omega⟩ ∧
    ((printTM blank inputAlpha h_blank w).runOnInput input k).headPos = (k : ℤ) ∧
    (∀ (j : ℕ) (hj : j < k),
      ((printTM blank inputAlpha h_blank w).runOnInput input k).tape (j : ℤ) =
        w[j]'(by omega)) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, fun j hj => absurd hj (by omega)⟩
    · simp [TM.runOnInput, TM.run, TM.initConfig, printTM]
    · simp [TM.runOnInput, TM.run, TM.initConfig, printTM]
  | succ k ih =>
    have hk' : k ≤ w.length := by omega
    obtain ⟨hstate, hhead, htape_w⟩ := ih hk'
    have hk_lt : k < w.length := by omega
    set ck := (printTM blank inputAlpha h_blank w).runOnInput input k with hck_def
    have hrun_succ : (printTM blank inputAlpha h_blank w).runOnInput input (k + 1) =
        (printTM blank inputAlpha h_blank w).step ck := by
      simp [TM.runOnInput, TM.run, hck_def]
    have h_not_halt : ¬(ck.state = (printTM blank inputAlpha h_blank w).qAccept ∨
        ck.state = (printTM blank inputAlpha h_blank w).qReject) := by
      simp only [hstate, printTM, Fin.mk.injEq]; omega
    have hstep_def : (printTM blank inputAlpha h_blank w).step ck =
        ⟨⟨k + 1, by omega⟩, (k : ℤ) + 1, Function.update ck.tape (k : ℤ) (w[k]'hk_lt)⟩ := by
      unfold TM.step
      simp only [h_not_halt, ite_false]
      simp only [printTM, hstate, dif_pos hk_lt, hhead]
    rw [hrun_succ, hstep_def]
    refine ⟨rfl, ?_, ?_⟩
    · norm_cast
    · intro j hj
      simp only [Function.update]
      split_ifs with heq
      · have : j = k := by omega
        subst this; rfl
      · exact htape_w j (by omega)

set_option maxHeartbeats 800000 in
/-- Correctness of `printTM`: on any input, after exactly `|w|` steps the printer
machine `P_w` halts (in fact accepts) and the first `|w|` tape cells (read off by
`Config.readTape`) spell out `w`. This realizes the `haltsWithOutput` spec
demanded by `TMEncoding`. -/
theorem printTM_haltsWithOutput (blank : Γ) (inputAlpha : Set Γ)
    (h_blank : blank ∉ inputAlpha) (w input : List Γ) :
    ∃ n : ℕ,
      (printTM blank inputAlpha h_blank w).isHaltConfig
        ((printTM blank inputAlpha h_blank w).runOnInput input n) ∧
      Config.readTape ((printTM blank inputAlpha h_blank w).runOnInput input n) w.length = w := by
  have hinv := printTM_invariant_any_input blank inputAlpha h_blank w input w.length le_rfl
  refine ⟨w.length, ?_, ?_⟩
  ·
    left
    simp only [TM.isAcceptConfig, printTM]
    exact hinv.1
  ·
    simp only [Config.readTape]
    have hlen : (List.range w.length).length = w.length := List.length_range
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.length_map, List.length_range] at hi1
      simp only [List.getElem_map, List.getElem_range]
      exact hinv.2.2 i hi1

end TuringMachine
