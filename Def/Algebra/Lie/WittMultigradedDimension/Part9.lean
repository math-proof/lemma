/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Dimension.Finite
import Def.Algebra.Lie.FreeLieMultihomogeneousComponent
import Def.Algebra.Lie.WittMultigradedValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Rotate
import Theorem.Combinatorics.Words.LyndonWord.Part14
import Lemma.Finset.Words.LyndonWord
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeAlgebra
import Theorem.Algebra.Lie.WittMultigradedDimension.Part9
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable def wittLyndonSpanFrom (K : Type) [Field K] {r : ℕ}
    (degree : Fin r → ℕ) (lower : List (Fin r)) :
    Submodule K (FreeLieAlgebra K (Fin r)) :=
  Submodule.span K {x | ∃ (w : List (Fin r)) (hw : IsLyndonWord w),
    wittWordContent w = degree ∧ lower ≤ w ∧ x = wittLyndonBracket K w hw}

def WittLyndonPair (r n : ℕ) :=
  {p : List (Fin r) × List (Fin r) //
    IsLyndonWord p.1 ∧ IsLyndonWord p.2 ∧ p.1 < p.2 ∧ p.1.length + p.2.length = n}

def wittLyndonPairEncode {r n : ℕ} (p : WittLyndonPair r n) :
    List.Vector (Fin r) n × Fin (n + 1) :=
  (⟨p.1.1 ++ p.1.2, by simpa using p.2.2.2.2⟩,
    ⟨p.1.1.length, by have := p.2.2.2.2; omega⟩)

end MetaMathlibExt
