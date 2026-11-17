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
public import Theorem.Combinatorics.Words.LyndonWord.Part2

@[expose] public section

open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

instance {r : ℕ} (degree : Fin r → ℕ) : Finite (WordsOfContent degree) :=
  Finite.of_injective (wittWordsToVector degree) (wittWordsToVector_injective degree)

noncomputable instance {r : ℕ} (degree : Fin r → ℕ) : Fintype (WordsOfContent degree) :=
  Fintype.ofFinite _

instance {r : ℕ} (degree : Fin r → ℕ) : Finite (LyndonWordsOfContent degree) :=
  Finite.of_injective (fun w => w.1) fun _ _ h => Subtype.ext h

noncomputable instance {r : ℕ} (degree : Fin r → ℕ) : Fintype (LyndonWordsOfContent degree) :=
  Fintype.ofFinite _

end MetaMathlibExt
