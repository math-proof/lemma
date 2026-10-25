/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.PNat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Def.NumberTheory.Recurrences.GolombLikeSequence.Part7
/-!
# Closed forms for Golomb-like sequences

This file proves existence, uniqueness, and the block closed form for strictly increasing
positive-integer solutions of `f (f n) = y * n + z`.
-/


namespace MetaMathlibExt

theorem glk_v_step
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (x : ℤ) (hx : 1 ≤ x) :
    glk_v y z hy hz (x + 1) = glk_v y z hy hz x + 1 ∨
      glk_v y z hy hz (x + 1) = glk_v y z hy hz x + y := by
  let k := glk_index y z hy hz x
  have hloc := glk_locate y z hy hz x hx
  change glk_l y z k ≤ x ∧ x < glk_l y z (k + 1) at hloc
  have hcpow : 0 < glk_c y z * y ^ k :=
    mul_pos (by exact (glk_c_spec y z hz hpar).1) (pow_pos (by omega) k)
  have hnext := glk_l_succ_eq_a_add y z hz hpar k
  have hvx := glk_v_of_mem y z hy hz x k hloc.1 hloc.2
  by_cases hblock : x + 1 < glk_l y z (k + 1)
  · have hvnext := glk_v_of_mem y z hy hz (x + 1) k (by omega) hblock
    by_cases hleft : x < glk_a y z k
    · left
      rw [hvx, hvnext]
      by_cases hleft' : x + 1 < glk_a y z k
      · simp [hleft, hleft']
        ring
      · have heq : x + 1 = glk_a y z k := by omega
        simp [hleft, heq]
        omega
    · right
      rw [hvx, hvnext]
      have hleft' : ¬x + 1 < glk_a y z k := by omega
      simp [hleft, hleft']
      ring
  · have hboundary : x + 1 = glk_l y z (k + 1) := by omega
    have hupp := glk_l_strict_step y z hy hz (k + 1)
    have hvnext := glk_v_of_mem y z hy hz (x + 1) (k + 1) (by omega) (by omega)
    have hnotleft : ¬x < glk_a y z k := by
      unfold glk_a at hnext ⊢
      nlinarith
    have hnextleft : x + 1 < glk_a y z (k + 1) := by
      rw [hboundary]
      unfold glk_a
      exact lt_add_of_pos_right _
        (mul_pos (lt_of_lt_of_le Int.zero_lt_one (glk_c_spec y z hz hpar).1)
          (pow_pos (by omega : 0 < y) (k + 1)))
    right
    rw [hvx, hvnext]
    rw [ite_eq_right hnotleft, ite_eq_left hnextleft]
    have hmid := glk_l_succ_eq_a_add y z hz hpar (k + 1)
    have hxEq : x = glk_l y z (k + 1) - 1 := by omega
    rw [hxEq, hmid]
    unfold glk_a at hnext ⊢
    rw [hnext, pow_succ]
    ring

theorem glk_v_comp
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (x : ℤ) (hx : 1 ≤ x) :
    glk_v y z hy hz (glk_v y z hy hz x) = y * x + z := by
  let k := glk_index y z hy hz x
  have hloc := glk_locate y z hy hz x hx
  change glk_l y z k ≤ x ∧ x < glk_l y z (k + 1) at hloc
  have hcpow : 0 < glk_c y z * y ^ k :=
    mul_pos (by exact (glk_c_spec y z hz hpar).1) (pow_pos (by omega) k)
  have hnext := glk_l_succ_eq_a_add y z hz hpar k
  have hvx := glk_v_of_mem y z hy hz x k hloc.1 hloc.2
  have hlrec : glk_l y z (k + 1) = y * glk_l y z k + z := by rw [glk_l]
  by_cases hleft : x < glk_a y z k
  · rw [hvx]
    simp only [hleft, ↓reduceIte]
    have hvlow : glk_l y z k ≤
        glk_l y z (k + 1) + x - glk_a y z k := by
      unfold glk_a at hnext ⊢
      nlinarith
    have hvupp : glk_l y z (k + 1) + x - glk_a y z k <
        glk_l y z (k + 1) := by omega
    rw [glk_v_of_mem y z hy hz _ k hvlow hvupp]
    have hvright : ¬glk_l y z (k + 1) + x - glk_a y z k < glk_a y z k := by
      unfold glk_a at hnext ⊢
      nlinarith
    rw [ite_eq_right hvright]
    unfold glk_a at hnext ⊢
    nlinarith
  · rw [hvx]
    simp only [hleft, ↓reduceIte]
    have hvlow : glk_l y z (k + 1) ≤
        glk_l y z (k + 1) + y * (x - glk_a y z k) := by
      nlinarith
    have hanext : glk_a y z (k + 1) =
        glk_l y z (k + 1) + glk_c y z * y ^ (k + 1) := by rfl
    have hvupp : glk_l y z (k + 1) + y * (x - glk_a y z k) <
        glk_l y z (k + 2) := by
      have hmid := glk_l_succ_eq_a_add y z hz hpar (k + 1)
      rw [hmid]
      unfold glk_a at hnext ⊢
      rw [pow_succ]
      nlinarith
    rw [glk_v_of_mem y z hy hz _ (k + 1) hvlow hvupp]
    have hvleft : glk_l y z (k + 1) + y * (x - glk_a y z k) <
        glk_a y z (k + 1) := by
      rw [hanext]
      unfold glk_a at hnext ⊢
      rw [pow_succ]
      nlinarith
    rw [ite_eq_left hvleft]
    have hmid := glk_l_succ_eq_a_add y z hz hpar (k + 1)
    rw [hmid]
    unfold glk_a at hnext ⊢
    rw [pow_succ]
    nlinarith [hlrec]

end MetaMathlibExt
