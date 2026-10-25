/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.PNat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Def.NumberTheory.Recurrences.GolombLikeSequence.Part3
/-!
# Closed forms for Golomb-like sequences

This file proves existence, uniqueness, and the block closed form for strictly increasing
positive-integer solutions of `f (f n) = y * n + z`.
-/


namespace MetaMathlibExt

theorem glk_l_succ_eq_a_add
    (y z : ℤ) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) (k : ℕ) :
    glk_l y z (k + 1) = glk_a y z k + glk_c y z * y ^ k := by
  rw [glk_a, glk_l_succ y z hz hpar k]
  ring

end MetaMathlibExt
