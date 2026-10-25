/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Def.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem highTempSwitch_input_sum (t : Sym2 V → ℝ)
    (S : Finset V) (o z : V) :
    (∑ p : ↥(highTempSwitchInputs G S o z),
        highTempSwitchInputWeight t p.1) =
      highTempSourceSum G.edgeFinset t (sourcePair o z) *
        highTempSourceSum (highTempInternalEdges G S) t ∅ := by
  classical
  let SF := highTempSourceSubgraphs G.edgeFinset (sourcePair o z)
  let SH := highTempSourceSubgraphs (highTempInternalEdges G S) ∅
  have hreindex :
      (∑ p ∈ highTempSwitchInputs G S o z,
          highTempSwitchInputWeight t p) =
        ∑ q ∈ SF ×ˢ SH,
          (∏ e ∈ q.1, t e) * ∏ e ∈ q.2, t e := by
    apply Finset.sum_bij (fun p _ => (p.F, p.H))
    · intro p hp
      rw [highTempSwitchInputs, Finset.mem_filter] at hp
      rw [Finset.mem_product]
      constructor
      · have hmem : p.F ∈ highTempSourceSubgraphs G.edgeFinset
            (sourcePair o z) := by
          rw [highTempSourceSubgraphs, Finset.mem_filter,
            Finset.mem_powerset]
          exact ⟨hp.2.1, hp.2.2.2.1⟩
        simpa only [SF] using hmem
      · have hmem : p.H ∈ highTempSourceSubgraphs
            (highTempInternalEdges G S) ∅ := by
          rw [highTempSourceSubgraphs, Finset.mem_filter,
            Finset.mem_powerset]
          exact ⟨hp.2.2.1, hp.2.2.2.2⟩
        simpa only [SH] using hmem
    · intro p hp q hq heq
      cases p
      cases q
      simp_all
    · intro q hq
      rw [Finset.mem_product] at hq
      have hF := hq.1
      have hH := hq.2
      dsimp only [SF] at hF
      dsimp only [SH] at hH
      rw [highTempSourceSubgraphs, Finset.mem_filter,
        Finset.mem_powerset] at hF hH
      let p : HighTempSwitchInput (V := V) := ⟨q.1, q.2⟩
      refine ⟨p, ?_, rfl⟩
      rw [highTempSwitchInputs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hF.1, hH.1, hF.2, hH.2⟩
    · intro p hp
      rfl
  calc
    (∑ p : ↥(highTempSwitchInputs G S o z),
        highTempSwitchInputWeight t p.1) =
        ∑ p ∈ highTempSwitchInputs G S o z,
          highTempSwitchInputWeight t p := by
            simpa only [Finset.attach_eq_univ] using
              Finset.sum_attach (highTempSwitchInputs G S o z)
                (highTempSwitchInputWeight t)
    _ = ∑ q ∈ SF ×ˢ SH,
          (∏ e ∈ q.1, t e) * ∏ e ∈ q.2, t e := hreindex
    _ = (∑ F ∈ SF, ∏ e ∈ F, t e) *
          ∑ H ∈ SH, ∏ e ∈ H, t e := by
            rw [Finset.sum_product, Finset.sum_mul_sum]
    _ = _ := by rfl

set_option maxHeartbeats 2000000 in

theorem highTempSwitch_output_sum (t : Sym2 V → ℝ)
    (S : Finset V) (o z : V) :
    (∑ r : ↥(highTempSwitchOutputs G S o z),
        highTempSwitchOutputWeight t r.1) =
      ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
        t s(x, y) * highTempSourceSum (highTempInternalEdges G S) t
            (sourcePair o x) *
          highTempSourceSum G.edgeFinset t (sourcePair y z) := by
  classical
  let T : Finset (V × V × Finset (Sym2 V) × Finset (Sym2 V)) :=
    Finset.univ.filter (fun q =>
      q.1 ∈ S ∧ q.2.1 ∉ S ∧
        q.2.2.1 ∈ highTempSourceSubgraphs (highTempInternalEdges G S)
          (sourcePair o q.1) ∧
        q.2.2.2 ∈ highTempSourceSubgraphs G.edgeFinset
          (sourcePair q.2.1 z))
  have hreindex :
      (∑ r ∈ highTempSwitchOutputs G S o z,
          highTempSwitchOutputWeight t r) =
        ∑ q ∈ T,
          (∏ e ∈ q.2.2.1, t e) * t s(q.1, q.2.1) *
            ∏ e ∈ q.2.2.2, t e := by
    apply Finset.sum_bij (fun r _ => (r.x, r.y, r.A, r.B))
    · intro r hr
      rw [highTempSwitchOutputs, Finset.mem_filter] at hr
      change (r.x, r.y, r.A, r.B) ∈ Finset.univ.filter (fun q =>
        q.1 ∈ S ∧ q.2.1 ∉ S ∧
          q.2.2.1 ∈ highTempSourceSubgraphs (highTempInternalEdges G S)
            (sourcePair o q.1) ∧
          q.2.2.2 ∈ highTempSourceSubgraphs G.edgeFinset
            (sourcePair q.2.1 z))
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hr.2.1, hr.2.2.1, ?_, ?_⟩
      · rw [highTempSourceSubgraphs, Finset.mem_filter,
          Finset.mem_powerset]
        exact ⟨hr.2.2.2.1, hr.2.2.2.2.2.1⟩
      · rw [highTempSourceSubgraphs, Finset.mem_filter,
          Finset.mem_powerset]
        exact ⟨hr.2.2.2.2.1, hr.2.2.2.2.2.2⟩
    · intro r hr u hu heq
      cases r
      cases u
      simp_all
    · intro q hq
      change q ∈ Finset.univ.filter (fun q =>
        q.1 ∈ S ∧ q.2.1 ∉ S ∧
          q.2.2.1 ∈ highTempSourceSubgraphs (highTempInternalEdges G S)
            (sourcePair o q.1) ∧
          q.2.2.2 ∈ highTempSourceSubgraphs G.edgeFinset
            (sourcePair q.2.1 z)) at hq
      rw [Finset.mem_filter] at hq
      rcases hq with ⟨_, hx, hy, hA, hB⟩
      let r : HighTempSwitchOutput (V := V) :=
        ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
      refine ⟨r, ?_, rfl⟩
      rw [highTempSwitchOutputs, Finset.mem_filter]
      rw [highTempSourceSubgraphs, Finset.mem_filter,
        Finset.mem_powerset] at hA hB
      exact ⟨Finset.mem_univ _, hx, hy,
        hA.1, hB.1, hA.2, hB.2⟩
    · intro r hr
      rfl
  rw [show (∑ r : ↥(highTempSwitchOutputs G S o z),
      highTempSwitchOutputWeight t r.1) =
      ∑ r ∈ highTempSwitchOutputs G S o z,
        highTempSwitchOutputWeight t r by
      simpa only [Finset.attach_eq_univ] using
        Finset.sum_attach (highTempSwitchOutputs G S o z)
          (highTempSwitchOutputWeight t)]
  rw [hreindex]
  unfold T
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  have hsum_mem (f : V → ℝ) :
      (∑ x ∈ S, f x) = ∑ x : V, if x ∈ S then f x else 0 := by
    have hs : S = Finset.univ.filter (fun x => x ∈ S) := by
      ext x
      simp
    calc
      (∑ x ∈ S, f x) =
          ∑ x ∈ Finset.univ.filter (fun x => x ∈ S), f x := by
            exact Finset.sum_congr hs (fun _ _ => rfl)
      _ = _ := Finset.sum_filter (s := (Finset.univ : Finset V))
        (p := fun x => x ∈ S) f
  have hsum_notMem (f : V → ℝ) :
      (∑ y ∈ Finset.univ \ S, f y) =
        ∑ y : V, if y ∉ S then f y else 0 := by
    calc
      (∑ y ∈ Finset.univ \ S, f y) =
          ∑ y ∈ Finset.univ.filter (fun y => y ∉ S), f y := by
            apply Finset.sum_congr
            · ext y
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
                Finset.mem_filter]
            · intros
              rfl
      _ = _ := Finset.sum_filter (s := (Finset.univ : Finset V))
        (p := fun y => y ∉ S) f
  have hsum_family (U : Finset (Finset (Sym2 V)))
      (f : Finset (Sym2 V) → ℝ) :
      (∑ A : Finset (Sym2 V), if A ∈ U then f A else 0) =
        ∑ A ∈ U, f A := by
    symm
    have hU : U = Finset.univ.filter (fun A => A ∈ U) := by
      ext A
      simp
    calc
      (∑ A ∈ U, f A) =
          ∑ A ∈ Finset.univ.filter (fun A => A ∈ U), f A := by
            exact Finset.sum_congr hU (fun _ _ => rfl)
      _ = _ := Finset.sum_filter (s := (Finset.univ :
        Finset (Finset (Sym2 V)))) (p := fun A => A ∈ U) f
  rw [hsum_mem]
  simp_rw [hsum_notMem]
  simp only [highTempSourceSum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ S
  · rw [if_pos hx]
    rw [Finset.sum_congr rfl]
    intro y _
    by_cases hy : y ∉ S
    · rw [if_pos hy]
      simp only [hx, hy, not_false_eq_true, true_and]
      let SA := highTempSourceSubgraphs (highTempInternalEdges G S)
        (sourcePair o x)
      let SB := highTempSourceSubgraphs G.edgeFinset (sourcePair y z)
      calc
        (∑ A : Finset (Sym2 V), ∑ B : Finset (Sym2 V),
            if A ∈ SA ∧ B ∈ SB then
              (∏ e ∈ A, t e) * t s(x, y) * ∏ e ∈ B, t e else 0) =
          ∑ A : Finset (Sym2 V), if A ∈ SA then
            (∑ B : Finset (Sym2 V), if B ∈ SB then
              (∏ e ∈ A, t e) * t s(x, y) * ∏ e ∈ B, t e else 0) else 0 := by
                apply Finset.sum_congr rfl
                intro A _
                by_cases hA : A ∈ SA
                · rw [if_pos hA]
                  apply Finset.sum_congr rfl
                  intro B _
                  by_cases hB : B ∈ SB <;> simp [hA, hB]
                · rw [if_neg hA]
                  simp only [hA, false_and, if_false,
                    Finset.sum_const_zero]
        _ = ∑ A ∈ SA, ∑ B ∈ SB,
              (∏ e ∈ A, t e) * t s(x, y) * ∏ e ∈ B, t e := by
                rw [hsum_family]
                apply Finset.sum_congr rfl
                intro A _
                rw [hsum_family]
        _ = (t s(x, y) * ∑ A ∈ SA, ∏ e ∈ A, t e) *
              ∑ B ∈ SB, ∏ e ∈ B, t e := by
                let WB := ∑ B ∈ SB, ∏ e ∈ B, t e
                calc
                  (∑ A ∈ SA, ∑ B ∈ SB,
                      (∏ e ∈ A, t e) * t s(x, y) * ∏ e ∈ B, t e) =
                    ∑ A ∈ SA, ((∏ e ∈ A, t e) * t s(x, y)) * WB := by
                      apply Finset.sum_congr rfl
                      intro A _
                      unfold WB
                      rw [Finset.mul_sum]
                  _ = (∑ A ∈ SA, (∏ e ∈ A, t e) * t s(x, y)) * WB := by
                      rw [Finset.sum_mul]
                  _ = _ := by
                      rw [← Finset.sum_mul]
                      ring
    · simp [hx, hy]
  · simp [hx]


theorem highTemp_sourceSum_simon (t : Sym2 V → ℝ) (ht : ∀ e, 0 ≤ t e)
    (S : Finset V) (o z : V) (ho : o ∈ S) (hz : z ∉ S) :
    highTempSourceSum G.edgeFinset t (sourcePair o z) *
        highTempSourceSum (highTempInternalEdges G S) t ∅ ≤
      ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
        t s(x, y) * highTempSourceSum (highTempInternalEdges G S) t
            (sourcePair o x) *
          highTempSourceSum G.edgeFinset t (sourcePair y z) := by
  rw [← highTempSwitch_input_sum G t S o z,
    ← highTempSwitch_output_sum G t S o z]
  exact highTempSwitch_sum_le G t ht S o z ho hz


theorem highTempSourceSum_zero_extension
    (I E : Finset (Sym2 V)) (hIE : I ⊆ E)
    (t t' : Sym2 V → ℝ)
    (hin : ∀ e ∈ I, t' e = t e)
    (hout : ∀ e ∈ E, e ∉ I → t' e = 0)
    (A : Finset V) :
    highTempSourceSum E t' A = highTempSourceSum I t A := by
  classical
  have hsub : highTempSourceSubgraphs I A ⊆
      highTempSourceSubgraphs E A := by
    intro F hF
    rw [highTempSourceSubgraphs, Finset.mem_filter,
      Finset.mem_powerset] at hF ⊢
    exact ⟨hF.1.trans hIE, hF.2⟩
  have hzero : ∀ F ∈ highTempSourceSubgraphs E A,
      F ∉ highTempSourceSubgraphs I A → (∏ e ∈ F, t' e) = 0 := by
    intro F hFE hFI
    rw [highTempSourceSubgraphs, Finset.mem_filter,
      Finset.mem_powerset] at hFE
    have hnsub : ¬ F ⊆ I := by
      intro hsubI
      apply hFI
      rw [highTempSourceSubgraphs, Finset.mem_filter,
        Finset.mem_powerset]
      exact ⟨hsubI, hFE.2⟩
    rw [Finset.not_subset] at hnsub
    obtain ⟨e, heF, heI⟩ := hnsub
    exact Finset.prod_eq_zero heF (hout e (hFE.1 heF) heI)
  have hext :
      (∑ F ∈ highTempSourceSubgraphs I A, ∏ e ∈ F, t' e) =
        ∑ F ∈ highTempSourceSubgraphs E A, ∏ e ∈ F, t' e :=
    Finset.sum_subset hsub hzero
  unfold highTempSourceSum
  rw [← hext]
  apply Finset.sum_congr rfl
  intro F hF
  apply Finset.prod_congr rfl
  intro e he
  have hFI : F ⊆ I := by
    rw [highTempSourceSubgraphs, Finset.mem_filter,
      Finset.mem_powerset] at hF
    exact hF.1
  exact hin e (hFI he)


theorem highTempSourceSum_couplingIn (beta : ℝ) (J : Sym2 V → ℝ)
    (S A : Finset V) :
    highTempSourceSum G.edgeFinset
        (fun e => Real.tanh (beta * couplingIn J S e)) A =
      highTempSourceSum (highTempInternalEdges G S)
        (fun e => Real.tanh (beta * J e)) A := by
  apply highTempSourceSum_zero_extension
    (highTempInternalEdges G S) G.edgeFinset
  · intro e he
    exact (mem_highTempInternalEdges G S e).mp he |>.1
  · intro e he
    have hins := (mem_highTempInternalEdges G S e).mp he |>.2
    simp [couplingIn, hins]
  · intro e heG heI
    have hninside : ¬ edgeInside S e := by
      intro h
      exact heI ((mem_highTempInternalEdges G S e).2 ⟨heG, h⟩)
    simp [couplingIn, hninside]


end Sharpness
end StatMech
