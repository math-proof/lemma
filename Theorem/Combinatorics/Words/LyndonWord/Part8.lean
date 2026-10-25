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
import Instance.Combinatorics.Words.LyndonWord.Part2
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

theorem wittRotate_injective {α : Type*} [LinearOrder α] {w : List α}
    (hw : IsLyndonWord w) {i j : ℕ} (hi : i < w.length) (hj : j < w.length)
    (hrotate : w.rotate i = w.rotate j) : i = j := by
  have aux : ∀ {a b : ℕ}, a < b → b < w.length →
      w.rotate a = w.rotate b → False := by
    intro a b hab hb hrot
    have ha : a ≤ w.length := (hab.trans hb).le
    have heq₁ : a + (w.length - a) = w.length := Nat.add_sub_of_le ha
    have heq₂ : b + (w.length - a) = w.length + (b - a) := by omega
    have hfix : w.rotate (b - a) = w := by
      calc
        w.rotate (b - a) = (w.rotate w.length).rotate (b - a) := by
          rw [w.rotate_length]
        _ = w.rotate (w.length + (b - a)) := w.rotate_rotate _ _
        _ = w.rotate (b + (w.length - a)) := by rw [heq₂]
        _ = (w.rotate b).rotate (w.length - a) := (w.rotate_rotate _ _).symm
        _ = (w.rotate a).rotate (w.length - a) := by rw [hrot]
        _ = w.rotate (a + (w.length - a)) := w.rotate_rotate _ _
        _ = w := by rw [heq₁, w.rotate_length]
    have hlt := hw.2 (b - a) (by omega) (by omega)
    rw [hfix] at hlt
    exact (lt_irrefl _ hlt)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact aux hij hj hrotate
  · exact aux hji hi hrotate.symm

/-- Every Lyndon word is primitive. -/
theorem isPrimitiveWord_of_isLyndonWord {α : Type*} [LinearOrder α] {w : List α}
    (hw : IsLyndonWord w) : IsPrimitiveWord w := by
  apply isPrimitiveWord_iff_nodup_cyclicPermutations.mpr
  refine ⟨hw.1, List.nodup_iff_injective_get.mpr ?_⟩
  intro i j hget
  apply Fin.ext
  apply wittRotate_injective hw
  · rw [← List.length_cyclicPermutations_of_ne_nil w hw.1]
    exact i.2
  · rw [← List.length_cyclicPermutations_of_ne_nil w hw.1]
    exact j.2
  · simpa only [List.get_cyclicPermutations] using hget

end MetaMathlibExt
