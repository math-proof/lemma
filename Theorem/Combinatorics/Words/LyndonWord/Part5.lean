/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Def.Algebra.Lie.WittMultigradedValue
import Def.Combinatorics.Words.PrimitiveWord
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.PeriodicityLemma
import Def.Combinatorics.Words.LyndonWord.Part5
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

theorem wittPeriod_pos {α : Type*} [DecidableEq α] (w : List α) (hw : w ≠ []) :
    0 < wittPeriod w hw := by
  exact (Nat.find_spec (wittExistsRotationPeriod w hw)).1

theorem wittRotate_period {α : Type*} [DecidableEq α] (w : List α) (hw : w ≠ []) :
    w.rotate (wittPeriod w hw) = w := by
  exact (Nat.find_spec (wittExistsRotationPeriod w hw)).2

theorem wittPeriod_le_length {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) :
    wittPeriod w hw ≤ w.length := by
  exact Nat.find_min' (wittExistsRotationPeriod w hw)
    ⟨List.length_pos_of_ne_nil hw, w.rotate_length⟩

theorem wittPeriod_min {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) {q : ℕ}
    (hq0 : 0 < q) (hq : w.rotate q = w) : wittPeriod w hw ≤ q := by
  exact Nat.find_min' (wittExistsRotationPeriod w hw) ⟨hq0, hq⟩

theorem wittRotate_mul_eq {α : Type*} (w : List α) {p : ℕ}
    (hp : w.rotate p = w) (q : ℕ) : w.rotate (p * q) = w := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ]
      rw [← w.rotate_rotate, ih, hp]

theorem wittPeriod_dvd_length {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : wittPeriod w hw ∣ w.length := by
  let p := wittPeriod w hw
  have hp0 : 0 < p := wittPeriod_pos w hw
  have hp : w.rotate p = w := wittRotate_period w hw
  have hrem : w.rotate (w.length % p) = w := by
    calc
      w.rotate (w.length % p) =
          (w.rotate (p * (w.length / p))).rotate (w.length % p) := by
            rw [wittRotate_mul_eq w hp]
      _ = w.rotate (p * (w.length / p) + w.length % p) := w.rotate_rotate _ _
      _ = w.rotate w.length := by
        congr 1
        simpa [add_comm] using (Nat.mod_add_div w.length p)
      _ = w := w.rotate_length
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra hne
  have hpos : 0 < w.length % p := Nat.pos_of_ne_zero hne
  have hle : p ≤ w.length % p := wittPeriod_min w hw hpos hrem
  exact (Nat.not_le_of_lt (Nat.mod_lt w.length hp0)) hle

theorem wittHasPeriod_of_rotate_eq {α : Type*} {w : List α} {p : ℕ}
    (hple : p ≤ w.length) (hrot : w.rotate p = w) : w.HasPeriod p := by
  rw [List.hasPeriod_iff_getElem?]
  intro i hi
  have hip : i + p < w.length := by omega
  have hiw : i < w.length := by omega
  have h := congr_arg (fun z : List α => z[i]?) hrot
  rw [List.getElem?_rotate hiw, Nat.mod_eq_of_lt hip] at h
  exact h.symm

end MetaMathlibExt
