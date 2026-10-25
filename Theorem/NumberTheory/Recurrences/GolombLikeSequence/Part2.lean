/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.PNat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Def.NumberTheory.Recurrences.GolombLikeSequence.Part2
/-!
# Closed forms for Golomb-like sequences

This file proves existence, uniqueness, and the block closed form for strictly increasing
positive-integer solutions of `f (f n) = y * n + z`.
-/


namespace MetaMathlibExt

theorem glk_l_one_le
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) : ∀ k, 1 ≤ glk_l y z k := by
  intro k
  induction k with
  | zero => simp [glk_l]
  | succ k ih =>
    rw [glk_l]
    nlinarith

theorem glk_l_strict_step
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (k : ℕ) :
    glk_l y z k < glk_l y z (k + 1) := by
  rw [glk_l]
  have hk := glk_l_one_le y z hy hz k
  nlinarith

theorem glk_l_strictMono
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) : StrictMono (glk_l y z) :=
  strictMono_nat_of_lt_succ (glk_l_strict_step y z hy hz)

theorem glk_l_growth
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (k : ℕ) :
    (k : ℤ) + 1 ≤ glk_l y z k := by
  induction k with
  | zero => simp [glk_l]
  | succ k ih =>
    have hstep := glk_l_strict_step y z hy hz k
    norm_num at ih ⊢
    omega

theorem glk_l_unbounded
    (y z x : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) :
    ∃ k : ℕ, x < glk_l y z (k + 1) := by
  refine ⟨x.toNat, ?_⟩
  have hg := glk_l_growth y z hy hz (x.toNat + 1)
  by_cases hx : 0 ≤ x
  · norm_num at hg ⊢
    simp [max_eq_left hx] at hg
    omega
  · have hto : x.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    rw [hto] at hg ⊢
    norm_num at hg ⊢
    omega

theorem glk_l_succ
    (y z : ℤ) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) (k : ℕ) :
    glk_l y z (k + 1) = glk_l y z k + 2 * glk_c y z * y ^ k := by
  have hc := (glk_c_spec y z hz hpar).2
  induction k with
  | zero =>
    simp [glk_l]
    omega
  | succ k ih =>
    have hrec : glk_l y z (k + 1) = y * glk_l y z k + z := by
      rw [glk_l]
    calc
      glk_l y z (k + 2) = y * glk_l y z (k + 1) + z := by rw [glk_l]
      _ = y * (glk_l y z k + 2 * glk_c y z * y ^ k) + z := by rw [ih]
      _ = (y * glk_l y z k + z) + 2 * glk_c y z * y ^ (k + 1) := by
        rw [pow_succ]
        ring
      _ = glk_l y z (k + 1) + 2 * glk_c y z * y ^ (k + 1) := by rw [hrec]

end MetaMathlibExt
