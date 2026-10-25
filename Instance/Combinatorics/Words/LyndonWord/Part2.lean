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
import Def.Combinatorics.Words.LyndonWord.Part8
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

instance {r : ℕ} (degree : Fin r → ℕ) : Finite (PrimitiveWordsOfContent degree) :=
  Finite.of_injective (fun w => w.1) fun _ _ h => Subtype.ext h

noncomputable instance {r : ℕ} (degree : Fin r → ℕ) :
    Fintype (PrimitiveWordsOfContent degree) :=
  Fintype.ofFinite _

end MetaMathlibExt
