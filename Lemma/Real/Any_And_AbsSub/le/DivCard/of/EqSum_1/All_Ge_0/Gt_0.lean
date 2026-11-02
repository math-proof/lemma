import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Initialize.Tactic.Attr.Basic
open Finset


private lemma approx [Fintype α] [DecidableEq α] {n : ℕ} {ν : α → ℝ} (hn : 0 < n) (hν : ∀ a, 0 ≤ ν a) (hsum : ∑ a, ν a = 1) :
  ∃ c : α → ℕ, ∑ a, c a = n ∧ ∀ a, |(c a : ℝ) / n - ν a| ≤ (Fintype.card α : ℝ) / n := by
  have hα : Nonempty α := by
    by_contra hempty
    have : IsEmpty α := not_nonempty_iff.mp hempty
    simp at hsum
  let a0 : α := Classical.choice hα
  let fl : α → ℕ := fun a => Nat.floor ((n : ℝ) * ν a)
  have hsum_fl : ∑ a, fl a ≤ n := by
    rw [← Nat.cast_le (α := ℝ), Nat.cast_sum]
    apply le_trans (sum_le_sum fun a _ => Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hν a)))
    rw [← mul_sum, hsum, mul_one]
  let r : ℕ := n - ∑ a, fl a
  let c : α → ℕ := fun a => fl a + if a = a0 then r else 0
  refine ⟨c, ?_, ?_⟩
  ·
    change ∑ a, (fl a + if a = a0 then r else 0) = n
    rw [sum_add_distrib]
    have hite : ∑ a, (if a = a0 then r else 0) = r := by
      rw [sum_eq_single a0]
      · simp
      ·
        intro b _ hb
        rw [ite_eq_right hb]
      ·
        intro h
        exact absurd (mem_univ a0) h
    rw [hite]
    exact Nat.add_sub_of_le hsum_fl
  ·
    have hr : (r : ℝ) = ∑ a, ((n : ℝ) * ν a - (fl a : ℝ)) := calc
      _ = (n : ℝ) - ∑ a, (fl a : ℝ) := by
        rw [eq_sub_iff_add_eq, add_comm, ← Nat.cast_sum, ← Nat.cast_add]
        exact_mod_cast Nat.add_sub_of_le hsum_fl
      _ = ∑ a, (n : ℝ) * ν a - ∑ a, (fl a : ℝ) := by
        apply congrArg (fun t => t - ∑ a, (fl a : ℝ))
        conv_lhs => rw [← mul_one (n : ℝ), ← hsum, mul_sum]
      _ = ∑ a, ((n : ℝ) * ν a - (fl a : ℝ)) := by
        rw [← sum_sub_distrib]
    have hrlt : (r : ℝ) < Fintype.card α := by
      rw [hr]
      calc
        _ < ∑ a : α, (1 : ℝ) := by
          apply sum_lt_sum_of_nonempty (univ_nonempty_iff.mpr hα)
          intro a _
          have hlt := Nat.lt_floor_add_one ((n : ℝ) * ν a)
          linarith
        _ = Fintype.card α := by
          simp [sum_const, card_univ]
    have hrle : r + 1 ≤ Fintype.card α := Nat.succ_le_of_lt (Nat.cast_lt.mp hrlt)
    intro a
    have hdiv : (fl a : ℝ) / n ≤ ν a := by
      rw [div_le_iff₀ (Nat.cast_pos.mpr hn), mul_comm]
      exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hν a))
    have hgap : ν a - (fl a : ℝ) / n < 1 / n := by
      rw [lt_div_iff₀ (Nat.cast_pos.mpr hn), sub_mul, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')]
      have hlt := Nat.lt_floor_add_one ((n : ℝ) * ν a)
      linarith
    have habs0 : |(fl a : ℝ) / n - ν a| ≤ 1 / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr hdiv)]
      linarith
    if ha : a = a0 then
      have hc : (c a : ℝ) = (fl a : ℝ) + r := by
        simp [c, ha]
      rw [hc]
      have hsplit : ((fl a : ℝ) + r) / n - ν a = ((fl a : ℝ) / n - ν a) + (r : ℝ) / n := by
        ring
      rw [hsplit]
      calc
        _ ≤ |(fl a : ℝ) / n - ν a| + |(r : ℝ) / n| := abs_add_le _ _
        _ = |(fl a : ℝ) / n - ν a| + (r : ℝ) / n := by
          rw [abs_of_nonneg (a := (r : ℝ) / n) (div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg n))]
        _ ≤ 1 / n + (r : ℝ) / n := add_le_add_left habs0 _
        _ = ((r : ℝ) + 1) / n := by
          ring
        _ ≤ (Fintype.card α : ℝ) / n := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
          exact_mod_cast hrle
    else
      have hc : c a = fl a := by
        simp [c, ha]
      rw [hc]
      apply habs0.trans
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact_mod_cast Fintype.card_pos_iff.mpr hα

/--
A probability vector on a finite alphabet is within `|α| / n` of some empirical frequency `c / n`.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
  {n : ℕ} {ν : α → ℝ}
-- given
  (hn : 0 < n)
  (hν : ∀ a, 0 ≤ ν a)
  (hsum : ∑ a, ν a = 1) :
-- imply
  ∃ c : α → ℕ, ∑ a, c a = n ∧ ∀ a, |(c a : ℝ) / n - ν a| ≤ (Fintype.card α : ℝ) / n :=
-- proof
  approx hn hν hsum


-- created on 2026-11-02
