/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.PNat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Def.NumberTheory.Recurrences.GolombLikeSequence.Part5
/-!
# Closed forms for Golomb-like sequences

This file proves existence, uniqueness, and the block closed form for strictly increasing
positive-integer solutions of `f (f n) = y * n + z`.
-/


namespace MetaMathlibExt

theorem glk_v_of_mem
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (x : ℤ) (k : ℕ)
    (hlow : glk_l y z k ≤ x) (hupp : x < glk_l y z (k + 1)) :
    glk_v y z hy hz x = if x < glk_a y z k then
      glk_l y z (k + 1) + x - glk_a y z k
    else
      glk_l y z (k + 1) + y * (x - glk_a y z k) := by
  rw [glk_v, glk_index_eq y z hy hz x k hlow hupp]

theorem glk_v_pos
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (x : ℤ) (hx : 1 ≤ x) : 0 < glk_v y z hy hz x := by
  let k := glk_index y z hy hz x
  have hloc := glk_locate y z hy hz x hx
  have hnext := glk_l_succ_eq_a_add y z hz hpar k
  have hcpow : 0 < glk_c y z * y ^ k := by
    exact mul_pos (by exact (glk_c_spec y z hz hpar).1) (pow_pos (by omega) k)
  change 0 < if x < glk_a y z k then
    glk_l y z (k + 1) + x - glk_a y z k
  else
    glk_l y z (k + 1) + y * (x - glk_a y z k)
  split_ifs with hleft
  · unfold glk_a at hnext ⊢
    nlinarith [hloc.1]
  · have hl := glk_l_one_le y z hy hz (k + 1)
    nlinarith

end MetaMathlibExt
