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
import Theorem.Combinatorics.Words.LyndonWord.Part11
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

noncomputable def wittLyndonRotationEquivPrimitive {r : ℕ}
    (degree : Fin r → ℕ) :
    LyndonWordsOfContent degree × Fin (∑ i, degree i) ≃
      PrimitiveWordsOfContent degree where
  toFun := wittRotateLyndon degree
  invFun := wittPrimitiveToLyndonRotation
  left_inv := wittPrimitiveTo_rotateLyndon degree
  right_inv := wittRotateLyndon_primitiveTo

end MetaMathlibExt
