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
public import Def.Combinatorics.Enumerative.RHorseNumberFubini


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

theorem rHorse_finSplit_inl {n r : ℕ} (hrn : r ≤ n) (i : Fin r) :
    rHorse_finSplit hrn (Sum.inl i) = Fin.castLE hrn i := by
  apply Fin.ext
  rfl

end MetaMathlibExt
