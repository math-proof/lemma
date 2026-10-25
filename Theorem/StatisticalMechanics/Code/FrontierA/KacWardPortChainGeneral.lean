/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwPortChainState_zero {n : ℕ} (b : Fin n → Fin 2) :
    kwPortChainState b 0 = 0 := by
  unfold kwPortChainState
  rw [List.Vector.get_zero, List.Vector.scanl_head]

theorem kwPortChainState_succ {n : ℕ} (b : Fin n → Fin 2)
    (i : Fin n) :
    kwPortChainState b i.succ = kwPortChainState b i.castSucc + b i := by
  unfold kwPortChainState
  simpa only [List.Vector.get_ofFn] using
    List.Vector.scanl_get (fun x bit : Fin 2 ↦ x + bit) (0 : Fin 2)
      (List.Vector.ofFn b) i


theorem kwPortChainState_unique {n : ℕ} (b : Fin n → Fin 2)
    (y : Fin (n + 1) → Fin 2) (hy0 : y 0 = 0)
    (hrec : ∀ i : Fin n, y i.succ = y i.castSucc + b i) :
    y = kwPortChainState b := by
  funext k
  induction k using Fin.induction with
  | zero => rw [hy0, kwPortChainState_zero]
  | succ i ih =>
      rw [hrec i, kwPortChainState_succ, ih]

theorem kw_fin_two_self_add (x : Fin 2) : x + x = 0 := by
  fin_cases x <;> decide


theorem kwPortChain_sum_eq_endpoints {n : ℕ} (b : Fin n → Fin 2)
    (y : Fin (n + 1) → Fin 2)
    (hrec : ∀ i : Fin n, y i.succ = y i.castSucc + b i) :
    (∑ i, b i) = y 0 + y (Fin.last n) := by
  have hb (i : Fin n) : b i = y i.succ + y i.castSucc := by
    have h := hrec i
    calc
      b i = b i + 0 := (add_zero _).symm
      _ = b i + (y i.castSucc + y i.castSucc) := by
        rw [kw_fin_two_self_add]
      _ = (y i.castSucc + b i) + y i.castSucc := by ac_rfl
      _ = y i.succ + y i.castSucc := by rw [h]
  rw [Finset.sum_congr rfl (fun i _ ↦ hb i), Finset.sum_add_distrib]
  have hsucc := Fin.sum_univ_succ y
  have hcast := Fin.sum_univ_castSucc y
  have hmiddle :
      (∑ i : Fin n, y i.succ) + ∑ i : Fin n, y i.castSucc =
        y 0 + y (Fin.last n) := by
    let A := ∑ i : Fin n, y i.succ
    let B := ∑ i : Fin n, y i.castSucc
    have hab : y 0 + A = B + y (Fin.last n) := by
      calc
        y 0 + A = ∑ i : Fin (n + 1), y i := hsucc.symm
        _ = B + y (Fin.last n) := hcast
    change A + B = y 0 + y (Fin.last n)
    calc
      A + B = (y 0 + (y 0 + A)) + B := by
        rw [← add_assoc, kw_fin_two_self_add, zero_add]
      _ = (y 0 + (B + y (Fin.last n))) + B := by rw [hab]
      _ = y 0 + y (Fin.last n) := by
        rw [add_assoc, add_assoc, add_comm (y (Fin.last n)) B,
          ← add_assoc B B, kw_fin_two_self_add, zero_add]
  exact hmiddle


theorem kwPortChainState_last_eq_zero_iff {n : ℕ} (b : Fin n → Fin 2) :
    kwPortChainState b (Fin.last n) = 0 ↔ (∑ i, b i) = 0 := by
  have hsum := kwPortChain_sum_eq_endpoints b (kwPortChainState b)
    (kwPortChainState_succ b)
  rw [kwPortChainState_zero, zero_add] at hsum
  rw [hsum]


theorem kwPortChain_existsUnique {n : ℕ} (b : Fin n → Fin 2) :
    (∑ i, b i) = 0 ↔ ∃! y : Fin (n + 1) → Fin 2,
      KWPortChainEven b y := by
  constructor
  · intro heven
    refine ⟨kwPortChainState b, ?_, ?_⟩
    · exact ⟨kwPortChainState_zero b, kwPortChainState_succ b,
        (kwPortChainState_last_eq_zero_iff b).2 heven⟩
    · intro y hy
      exact kwPortChainState_unique b y hy.1 hy.2.1
  · rintro ⟨y, hy, -⟩
    have hsum := kwPortChain_sum_eq_endpoints b y hy.2.1
    rw [hy.1, hy.2.2, add_zero] at hsum
    exact hsum


end StatMech.FrontierA
