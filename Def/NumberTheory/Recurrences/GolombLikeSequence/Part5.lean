/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.PNat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Theorem.NumberTheory.Recurrences.GolombLikeSequence.Part4
/-!
# Closed forms for Golomb-like sequences

This file proves existence, uniqueness, and the block closed form for strictly increasing
positive-integer solutions of `f (f n) = y * n + z`.
-/


namespace MetaMathlibExt

noncomputable def glk_v
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (x : ℤ) : ℤ :=
  let k := glk_index y z hy hz x
  if x < glk_a y z k then
    glk_l y z (k + 1) + x - glk_a y z k
  else
    glk_l y z (k + 1) + y * (x - glk_a y z k)

end MetaMathlibExt
