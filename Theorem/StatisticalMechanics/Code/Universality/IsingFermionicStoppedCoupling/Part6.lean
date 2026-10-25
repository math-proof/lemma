/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part6


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem choiceNoHitAllProjection_injective
    (t : Nat) (start level : Int) :
    Function.Injective (choiceNoHitAllProjection t start level) := by
  intro a b h
  have hx : a.1.1.map Prod.fst = b.1.1.map Prod.fst :=
    congrArg (fun z => z.1.1) h
  have hy : a.1.1.map Prod.snd = b.1.1.map Prod.snd :=
    congrArg (fun z => z.2.1) h
  apply Subtype.ext
  apply Subtype.ext
  exact prodBits_injective_full hx hy

theorem natCard_choiceNoHitAll_le_horizontal_mul_pow
    (t : Nat) (start level : Int) :
    Nat.card (IsingLeapfrogChoiceNoHitAll t start level) ≤
      Nat.card (IsingHorizontalNoHitFamily t start level) * 2 ^ t := by
  calc
    _ ≤ Nat.card (IsingHorizontalNoHitFamily t start level ×
        {ys : List Bool // ys.length = t}) :=
      Nat.card_le_card_of_injective (choiceNoHitAllProjection t start level)
        (choiceNoHitAllProjection_injective t start level)
    _ = _ := by
      rw [Nat.card_prod]
      congr 1
      change Nat.card (List.Vector Bool t) = 2 ^ t
      rw [Nat.card_congr (Equiv.vectorEquivFin Bool t),
        Nat.card_eq_fintype_card, Fintype.card_fun]
      simp

theorem sum_mul_eq_last_partial_add
    (a b : Nat → Real) (N : Nat) :
    (∑ k ∈ Finset.range (N + 1), a k * b k) =
      a N * (∑ k ∈ Finset.range (N + 1), b k) +
        ∑ k ∈ Finset.range N,
          (a k - a (k + 1)) * (∑ j ∈ Finset.range (k + 1), b j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        (∑ k ∈ Finset.range (N + 1 + 1), a k * b k) =
            (∑ k ∈ Finset.range (N + 1), a k * b k) +
              a (N + 1) * b (N + 1) := by rw [Finset.sum_range_succ]
        _ = (a N * (∑ k ∈ Finset.range (N + 1), b k) +
              ∑ k ∈ Finset.range N,
                (a k - a (k + 1)) *
                  (∑ j ∈ Finset.range (k + 1), b j)) +
              a (N + 1) * b (N + 1) := by rw [ih]
        _ = a (N + 1) * (∑ k ∈ Finset.range (N + 1 + 1), b k) +
              ∑ k ∈ Finset.range (N + 1),
                (a k - a (k + 1)) *
                  (∑ j ∈ Finset.range (k + 1), b j) := by
            have hbSucc : (∑ k ∈ Finset.range (N + 1 + 1), b k) =
                (∑ k ∈ Finset.range (N + 1), b k) + b (N + 1) := by
              rw [Finset.sum_range_succ]
            have hdSucc :
                (∑ k ∈ Finset.range (N + 1),
                  (a k - a (k + 1)) *
                    (∑ j ∈ Finset.range (k + 1), b j)) =
                  (∑ k ∈ Finset.range N,
                    (a k - a (k + 1)) *
                      (∑ j ∈ Finset.range (k + 1), b j)) +
                    (a N - a (N + 1)) *
                      (∑ j ∈ Finset.range (N + 1), b j) := by
              rw [Finset.sum_range_succ]
            rw [hbSucc, hdSucc]
            ring

theorem last_mul_add_sum_diff_eq_sum
    (a : Nat → Real) (N : Nat) :
    a N * (N + 1 : Nat) +
        ∑ k ∈ Finset.range N, (a k - a (k + 1)) * (k + 1 : Nat) =
      ∑ k ∈ Finset.range (N + 1), a k := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        a (N + 1) * (N + 1 + 1 : Nat) +
              ∑ k ∈ Finset.range (N + 1),
                (a k - a (k + 1)) * (k + 1 : Nat) =
            a (N + 1) * (N + 1 + 1 : Nat) +
              ((∑ k ∈ Finset.range N,
                (a k - a (k + 1)) * (k + 1 : Nat)) +
                (a N - a (N + 1)) * (N + 1 : Nat)) := by
              rw [Finset.sum_range_succ]
        _ = (a N * (N + 1 : Nat) +
              ∑ k ∈ Finset.range N,
                (a k - a (k + 1)) * (k + 1 : Nat)) +
              a (N + 1) := by
            push_cast
            ring
        _ = (∑ k ∈ Finset.range (N + 1), a k) + a (N + 1) := by
            rw [ih]
        _ = ∑ k ∈ Finset.range (N + 1 + 1), a k := by
            exact (Finset.sum_range_succ a (N + 1)).symm


theorem antitoneWeight_sum_le_uniform
    (a b : Nat → Real) (N : Nat) (c : Real)
    (ha0 : ∀ k, k ≤ N → 0 ≤ a k)
    (hadec : ∀ k, k < N → a (k + 1) ≤ a k)
    (hb : ∀ k, k ≤ N →
      ∑ j ∈ Finset.range (k + 1), b j ≤ c * (k + 1 : Nat)) :
    (∑ k ∈ Finset.range (N + 1), a k * b k) ≤
      c * ∑ k ∈ Finset.range (N + 1), a k := by
  rw [sum_mul_eq_last_partial_add]
  calc
    a N * (∑ k ∈ Finset.range (N + 1), b k) +
        ∑ k ∈ Finset.range N,
          (a k - a (k + 1)) * (∑ j ∈ Finset.range (k + 1), b j) ≤
      a N * (c * (N + 1 : Nat)) +
        ∑ k ∈ Finset.range N,
          (a k - a (k + 1)) * (c * (k + 1 : Nat)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hb N (le_refl _)) (ha0 N (le_refl _))
      · apply Finset.sum_le_sum
        intro k hk
        have hkN : k < N := Finset.mem_range.mp hk
        exact mul_le_mul_of_nonneg_left (hb k hkN.le)
          (sub_nonneg.mpr (hadec k hkN))
    _ = c * (a N * (N + 1 : Nat) +
        ∑ k ∈ Finset.range N,
          (a k - a (k + 1)) * (k + 1 : Nat)) := by
      rw [mul_add, Finset.mul_sum]
      apply congrArg₂ (· + ·) (by ring)
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = c * ∑ k ∈ Finset.range (N + 1), a k := by
      rw [last_mul_add_sum_diff_eq_sum]

theorem one_div_sqrt_succ_le_twice_diff (k : Nat) :
    1 / Real.sqrt (k + 1 : Real) ≤
      2 * (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) := by
  have hk0 : 0 ≤ (k : Real) := by positivity
  have hk1 : 0 ≤ (k + 1 : Real) := by positivity
  have hA : 0 < Real.sqrt (k + 1 : Real) := Real.sqrt_pos.2 (by positivity)
  have hB : Real.sqrt (k : Real) ≤ Real.sqrt (k + 1 : Real) := by
    exact Real.sqrt_le_sqrt (by norm_num)
  have hprod :
      (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) *
        (Real.sqrt (k + 1 : Real) + Real.sqrt (k : Real)) = 1 := by
    rw [show (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) *
        (Real.sqrt (k + 1 : Real) + Real.sqrt (k : Real)) =
      Real.sqrt (k + 1 : Real) ^ 2 - Real.sqrt (k : Real) ^ 2 by ring]
    rw [Real.sq_sqrt hk1, Real.sq_sqrt hk0]
    norm_num
  apply (div_le_iff₀ hA).2
  calc
    1 = (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) *
        (Real.sqrt (k + 1 : Real) + Real.sqrt (k : Real)) := hprod.symm
    _ ≤ (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) *
        (2 * Real.sqrt (k + 1 : Real)) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · linarith
    _ = 2 * (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) *
        Real.sqrt (k + 1 : Real) := by ring

theorem sum_one_div_sqrt_succ_le (N : Nat) :
    (∑ k ∈ Finset.range (N + 1), 1 / Real.sqrt (k + 1 : Real)) ≤
      2 * Real.sqrt (N + 1 : Real) := by
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1),
        2 * (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact one_div_sqrt_succ_le_twice_diff k
    _ = 2 * ∑ k ∈ Finset.range (N + 1),
        (Real.sqrt (k + 1 : Real) - Real.sqrt (k : Real)) := by
      rw [Finset.mul_sum]
    _ = 2 * (Real.sqrt (N + 1 : Real) - Real.sqrt (0 : Real)) := by
      have htel := Finset.sum_range_sub
        (fun k : Nat => Real.sqrt (k : Real)) (N + 1)
      norm_num [Nat.cast_add, Nat.cast_one] at htel
      rw [Finset.sum_sub_distrib, htel]
      norm_num
    _ = 2 * Real.sqrt (N + 1 : Real) := by norm_num


theorem ballotWeight_firstHit_sum_le
    (rho N : Nat) (b : Nat → Real) (hρ : 0 < rho)
    (hN : N ≤ rho * rho)
    (hb : ∀ k, k ≤ N →
      ∑ j ∈ Finset.range (k + 1), b j ≤
        (k + 1 : Real) / (rho : Real) ^ 2) :
    (∑ k ∈ Finset.range (N + 1),
      (4 / Real.sqrt (k + 1 : Real)) * b k) ≤
        16 / (rho : Real) := by
  let a : Nat → Real := fun k => 4 / Real.sqrt (k + 1 : Real)
  let c : Real := 1 / (rho : Real) ^ 2
  have ha0 : ∀ k, k ≤ N → 0 ≤ a k := by
    intro k hk
    dsimp [a]
    positivity
  have hadec : ∀ k, k < N → a (k + 1) ≤ a k := by
    intro k hk
    dsimp [a]
    apply div_le_div_of_nonneg_left (by norm_num)
      (Real.sqrt_pos.2 (by positivity))
    exact Real.sqrt_le_sqrt (by norm_num)
  have hb' : ∀ k, k ≤ N →
      ∑ j ∈ Finset.range (k + 1), b j ≤ c * (k + 1 : Nat) := by
    intro k hk
    have h := hb k hk
    dsimp [c]
    calc
      _ ≤ (k + 1 : Real) / (rho : Real) ^ 2 := h
      _ = (1 / (rho : Real) ^ 2) * (k + 1 : Nat) := by
        push_cast
        ring
  have hmajor := antitoneWeight_sum_le_uniform a b N c ha0 hadec hb'
  have hsum :
      (∑ k ∈ Finset.range (N + 1), a k) ≤
        16 * (rho : Real) := by
    have hinv := sum_one_div_sqrt_succ_le N
    have hsqrt : Real.sqrt (N + 1 : Real) ≤ (rho + 1 : Nat) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hNR : N + 1 ≤ (rho + 1) * (rho + 1) := by
          nlinarith
        have hNR' : (N + 1 : Real) ≤ ((rho + 1 : Nat) : Real) ^ 2 := by
          exact_mod_cast (show N + 1 ≤ (rho + 1) ^ 2 by
            simpa [pow_two] using hNR)
        exact hNR' 
    have hrho : (rho + 1 : Nat) ≤ 2 * rho := by omega
    have hsqrt' : Real.sqrt (N + 1 : Real) ≤ 2 * (rho : Real) := by
      exact le_trans hsqrt (by exact_mod_cast hrho)
    dsimp [a]
    calc
      (∑ k ∈ Finset.range (N + 1), 4 / Real.sqrt (k + 1 : Real)) =
          4 * ∑ k ∈ Finset.range (N + 1),
            1 / Real.sqrt (k + 1 : Real) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ 4 * (2 * Real.sqrt (N + 1 : Real)) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ ≤ 16 * (rho : Real) := by nlinarith
  dsimp [a] at hmajor
  calc
    _ ≤ c * ∑ k ∈ Finset.range (N + 1), a k := hmajor
    _ ≤ c * (16 * (rho : Real)) := by
      apply mul_le_mul_of_nonneg_left hsum
      dsimp [c]
      positivity
    _ = 16 / (rho : Real) := by
      dsimp [c]
      have hρReal : (rho : Real) ≠ 0 := by positivity
      field_simp

end
end StatMech.Universality
