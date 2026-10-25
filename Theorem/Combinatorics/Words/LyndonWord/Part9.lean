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
import Def.Combinatorics.Words.LyndonWord.Part9
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

theorem wittMinRotation_isRotated {α : Type*} [LinearOrder α] (w : List α) :
    wittMinRotation w ~r w := by
  rw [← List.mem_cyclicPermutations_iff]
  exact List.min_mem (List.cyclicPermutations_ne_nil w)

theorem wittMinRotation_isPrimitive {α : Type*} [LinearOrder α] {w : List α}
    (hw : IsPrimitiveWord w) : IsPrimitiveWord (wittMinRotation w) := by
  let hrot := wittMinRotation_isRotated w
  apply isPrimitiveWord_iff_nodup_cyclicPermutations.mpr
  constructor
  · intro hnil
    have hwrot : w ~r [] := by simpa [hnil] using hrot.symm
    exact hw.1 (List.isRotated_nil_iff.mp hwrot)
  · exact hrot.cyclicPermutations.nodup_iff.mpr
      (isPrimitiveWord_iff_nodup_cyclicPermutations.mp hw).2

theorem wittMinRotation_isLyndon {α : Type*} [LinearOrder α] {w : List α}
    (hw : IsPrimitiveWord w) : IsLyndonWord (wittMinRotation w) := by
  refine ⟨(wittMinRotation_isPrimitive hw).1, fun k hk0 hk => ?_⟩
  have hrot := wittMinRotation_isRotated w
  have hmem : (wittMinRotation w).rotate k ∈ w.cyclicPermutations := by
    rw [List.mem_cyclicPermutations_iff]
    exact (List.IsRotated.forall (wittMinRotation w) k).trans hrot
  have hle : wittMinRotation w ≤ (wittMinRotation w).rotate k :=
    List.min_le_of_mem hmem
  have hne := rotate_ne_of_isPrimitiveWord (wittMinRotation_isPrimitive hw) hk0 hk
  exact lt_of_le_of_ne hle hne.symm

theorem wittWordContent_minRotation {r : ℕ} (w : List (Fin r)) :
    wittWordContent (wittMinRotation w) = wittWordContent w := by
  funext i
  exact (wittMinRotation_isRotated w).perm.count_eq i

end MetaMathlibExt
