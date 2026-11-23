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
public import Theorem.Combinatorics.Words.LyndonWord.Part3
@[expose] public section

open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

abbrev WittPositiveLetter {r : ℕ} (degree : Fin r → ℕ) :=
  {i : Fin r // 0 < degree i}

end MetaMathlibExt
