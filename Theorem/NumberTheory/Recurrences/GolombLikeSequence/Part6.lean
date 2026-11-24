module
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic
public import Def.NumberTheory.Recurrences.GolombLikeSequence.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Closed forms for Golomb-like sequences

This file proves existence, uniqueness, and the block closed form for strictly increasing
positive-integer solutions of `f (f n) = y * n + z`.
-/
namespace MetaMathlibExt

@[simp] theorem glk_toPNat_val (x : ℤ) (hx : 0 < x) :
    (↑((glk_toPNat x hx).val) : ℤ) = x := by
  simp [glk_toPNat, Int.toNat_of_nonneg hx.le]

end MetaMathlibExt
