/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic
public import Theorem.NumberTheory.Recurrences.GolombLikeSequence.Part3

@[expose] public section

/-!
# Closed forms for Golomb-like sequences

This file proves existence, uniqueness, and the block closed form for strictly increasing
positive-integer solutions of `f (f n) = y * n + z`.
-/


namespace MetaMathlibExt

noncomputable def glk_index
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (x : ℤ) : ℕ :=
  Nat.find (glk_l_unbounded y z x hy hz)

end MetaMathlibExt
