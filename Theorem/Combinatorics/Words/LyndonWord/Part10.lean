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
import Def.Combinatorics.Words.LyndonWord.Part10
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

theorem wittMinRotation_rotate_index {α : Type*} [LinearOrder α]
    {w : List α} (hw : IsPrimitiveWord w) :
    (wittMinRotation w).rotate (wittMinRotationIndex hw) = w := by
  let hrot := wittMinRotation_isRotated w
  let k := Classical.choose hrot
  have hk : (wittMinRotation w).rotate k = w := Classical.choose_spec hrot
  have hlen : (wittMinRotation w).length = w.length := hrot.perm.length_eq
  change (wittMinRotation w).rotate (k % w.length) = w
  rw [← hlen, List.rotate_mod]
  exact hk

theorem length_wordsOfContent {r : ℕ} {degree : Fin r → ℕ}
    (w : WordsOfContent degree) : w.1.length = ∑ i, degree i := by
  rw [← sum_wittWordContent, w.2]

theorem wittWordContent_rotate {r : ℕ} (w : List (Fin r)) (k : ℕ) :
    wittWordContent (w.rotate k) = wittWordContent w := by
  funext i
  exact (List.rotate_perm w k).count_eq i

theorem isPrimitiveWord_rotate {α : Type*} {w : List α}
    (hw : IsPrimitiveWord w) (k : ℕ) : IsPrimitiveWord (w.rotate k) := by
  let hrot := List.IsRotated.forall w k
  apply isPrimitiveWord_iff_nodup_cyclicPermutations.mpr
  constructor
  · exact List.rotate_eq_nil_iff.not.mpr hw.1
  · exact hrot.cyclicPermutations.nodup_iff.mpr
      (isPrimitiveWord_iff_nodup_cyclicPermutations.mp hw).2

end MetaMathlibExt
