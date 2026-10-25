/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.PNat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Theorem.NumberTheory.Recurrences.GolombLikeSequence.Part6
/-!
# Closed forms for Golomb-like sequences

This file proves existence, uniqueness, and the block closed form for strictly increasing
positive-integer solutions of `f (f n) = y * n + z`.
-/


namespace MetaMathlibExt

noncomputable def glk_f
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    ℕ+ → ℕ+ := fun n =>
  glk_toPNat (glk_v y z hy hz n.val)
    (glk_v_pos y z hy hz hpar n.val (by exact_mod_cast n.pos))

end MetaMathlibExt
