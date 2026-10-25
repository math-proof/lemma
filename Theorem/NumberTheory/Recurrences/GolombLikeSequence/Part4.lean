/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.PNat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Def.NumberTheory.Recurrences.GolombLikeSequence.Part4
/-!
# Closed forms for Golomb-like sequences

This file proves existence, uniqueness, and the block closed form for strictly increasing
positive-integer solutions of `f (f n) = y * n + z`.
-/


namespace MetaMathlibExt

theorem glk_locate
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (x : ℤ) (hx : 1 ≤ x) :
    glk_l y z (glk_index y z hy hz x) ≤ x ∧
      x < glk_l y z (glk_index y z hy hz x + 1) := by
  let H := glk_l_unbounded y z x hy hz
  change glk_l y z (Nat.find H) ≤ x ∧ x < glk_l y z (Nat.find H + 1)
  refine ⟨?_, Nat.find_spec H⟩
  cases hk : Nat.find H with
  | zero => simp [glk_l, hx]
  | succ k =>
    have hklt : k < Nat.find H := by omega
    have hmin := Nat.find_min H hklt
    change ¬x < glk_l y z (k + 1) at hmin
    simpa [hk] using le_of_not_gt hmin

theorem glk_index_eq
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (x : ℤ) (k : ℕ)
    (hlow : glk_l y z k ≤ x) (hupp : x < glk_l y z (k + 1)) :
    glk_index y z hy hz x = k := by
  unfold glk_index
  apply (Nat.find_eq_iff (glk_l_unbounded y z x hy hz)).2
  refine ⟨hupp, ?_⟩
  intro n hn hbad
  have hmono := (glk_l_strictMono y z hy hz).monotone
  have hle : glk_l y z (n + 1) ≤ glk_l y z k := by
    apply hmono
    omega
  omega

end MetaMathlibExt
