module
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Rat.Defs
public import Def.Combinatorics.Enumerative.FubiniNumber
public import Theorem.Finset.Enumerative.FubiniNumber
public import Theorem.Finset.Enumerative.StirlingMatrices
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.StirlingMatrices
public import Theorem.Combinatorics.Enumerative.RHorseNumberFubini.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
