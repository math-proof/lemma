/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Rat.Defs
import Def.Combinatorics.Enumerative.FubiniNumber
import Lemma.Finset.Enumerative.FubiniNumber
import Lemma.Finset.Enumerative.StirlingMatrices
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.StirlingMatrices
import Theorem.Combinatorics.Enumerative.RHorseNumberFubini.Part2
/-! # r-horse numbers via Stirling-weighted Fubini values

This file proves the formula for `r`-horse numbers as a signed first-kind Stirling transform of
Fubini numbers.
-/


namespace MetaMathlibExt

open scoped BigOperators

def rHorse_strictMonoEquivFinset (r k : ℕ) :
    { f : Fin r → Fin k // StrictMono f } ≃
      { s : Finset (Fin k) // s.card = r } where
  toFun f := ⟨Finset.image f.1 Finset.univ, by
    rw [Finset.card_image_of_injective _ f.property.injective, Finset.card_univ,
      Fintype.card_fin]⟩
  invFun s := ⟨s.1.orderEmbOfFin s.2, (s.1.orderEmbOfFin s.2).strictMono⟩
  left_inv f := by
    apply Subtype.ext
    symm
    apply Finset.orderEmbOfFin_unique
    · intro i
      simp
    · exact f.property
  right_inv s := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ s.1 s.2

end MetaMathlibExt
