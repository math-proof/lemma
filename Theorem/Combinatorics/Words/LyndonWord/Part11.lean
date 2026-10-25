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
import Def.Combinatorics.Words.LyndonWord.Part11
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

theorem wittRotateLyndon_primitiveTo {r : ℕ} {degree : Fin r → ℕ}
    (w : PrimitiveWordsOfContent degree) :
    wittRotateLyndon degree (wittPrimitiveToLyndonRotation w) = w := by
  apply Subtype.ext
  apply Subtype.ext
  change (wittMinRotation w.1.1).rotate (wittMinRotationIndex w.2) = w.1.1
  exact wittMinRotation_rotate_index w.2

theorem eq_of_isLyndonWord_of_isRotated {α : Type*} [LinearOrder α]
    {u v : List α} (hu : IsLyndonWord u) (hv : IsLyndonWord v) (hrot : u ~r v) : u = v := by
  have le_of_rotated : ∀ {a b : List α}, IsLyndonWord a → a ~r b → a ≤ b := by
    intro a b ha hab
    obtain ⟨k, rfl⟩ := hab
    have hlen : 0 < a.length := List.length_pos_of_ne_nil ha.1
    by_cases hk0 : k % a.length = 0
    · rw [← List.rotate_mod, hk0, List.rotate_zero]
    · exact le_of_lt <| (List.rotate_mod a k) ▸
        ha.2 (k % a.length) (Nat.pos_of_ne_zero hk0) (Nat.mod_lt k hlen)
  exact le_antisymm (le_of_rotated hu hrot) (le_of_rotated hv hrot.symm)

theorem wittMinRotation_rotate_eq_of_lyndon {α : Type*} [LinearOrder α]
    {w : List α} (hw : IsLyndonWord w) (k : ℕ) :
    wittMinRotation (w.rotate k) = w := by
  have hprimitive := isPrimitiveWord_of_isLyndonWord hw
  apply eq_of_isLyndonWord_of_isRotated
    (wittMinRotation_isLyndon (isPrimitiveWord_rotate hprimitive k)) hw
  exact (wittMinRotation_isRotated (w.rotate k)).trans (List.IsRotated.forall w k)

theorem wittPrimitiveTo_rotateLyndon {r : ℕ} (degree : Fin r → ℕ)
    (p : LyndonWordsOfContent degree × Fin (∑ i, degree i)) :
    wittPrimitiveToLyndonRotation (wittRotateLyndon degree p) = p := by
  rcases p with ⟨w, k⟩
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    exact wittMinRotation_rotate_eq_of_lyndon w.2 k
  · apply Fin.ext
    change (wittMinRotationIndex
      (isPrimitiveWord_rotate (isPrimitiveWord_of_isLyndonWord w.2) k)).1 = k.1
    apply wittRotate_injective w.2
    · simpa using (wittMinRotationIndex
        (isPrimitiveWord_rotate (isPrimitiveWord_of_isLyndonWord w.2) k)).2
    · rw [length_wordsOfContent w.1]
      exact k.2
    · have hrotate := wittMinRotation_rotate_index
          (isPrimitiveWord_rotate (isPrimitiveWord_of_isLyndonWord w.2) k)
      rw [wittMinRotation_rotate_eq_of_lyndon w.2 k] at hrotate
      exact hrotate

end MetaMathlibExt
