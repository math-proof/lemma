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
/-! # r-horse numbers via Stirling-weighted Fubini values

This file proves the formula for `r`-horse numbers as a signed first-kind Stirling transform of
Fubini numbers.
-/


namespace MetaMathlibExt

open scoped BigOperators

def rHorse_finSplit {n r : ℕ} (hrn : r ≤ n) :
    Fin r ⊕ Fin (n - r) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hrn))

end MetaMathlibExt
