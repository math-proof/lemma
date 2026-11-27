module
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic
public import Theorem.NumberTheory.Recurrences.GolombLikeSequence.Part5
public import Notation.Data.PNat


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

def glk_toPNat (x : ℤ) (hx : 0 < x) : ℕ⁺ :=
  ⟨x.toNat, by
    have hcast := Int.toNat_of_nonneg hx.le
    apply Int.natCast_pos.mp
    simpa [hcast] using hx⟩

end MetaMathlibExt
