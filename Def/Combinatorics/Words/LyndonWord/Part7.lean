module
public import Def.Algebra.Lie.WittMultigradedValue
public import Def.Combinatorics.Words.PrimitiveWord
public import Mathlib.Data.List.Rotate
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.PeriodicityLemma
public import Theorem.Combinatorics.Words.LyndonWord.Part6
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/
namespace MetaMathlibExt

noncomputable def wittRoot {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : List α :=
  w.take (wittPeriod w hw)

noncomputable def wittExponent {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : ℕ :=
  w.length / wittPeriod w hw

end MetaMathlibExt
