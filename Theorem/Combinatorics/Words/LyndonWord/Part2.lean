/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Def.Algebra.Lie.WittMultigradedValue
public import Def.Combinatorics.Words.PrimitiveWord
public import Mathlib.Data.List.Rotate
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.PeriodicityLemma
public import Def.Combinatorics.Words.LyndonWord.Part2
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/

public section


namespace MetaMathlibExt

theorem wittWordsToVector_injective {r : ℕ} (degree : Fin r → ℕ) :
    Function.Injective (wittWordsToVector degree) := by
  intro u v h
  apply Subtype.ext
  exact congr_arg (fun z : List.Vector (Fin r) (∑ i, degree i) => z.1) h

end MetaMathlibExt
