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
import Theorem.Combinatorics.Enumerative.RHorseNumberFubini
/-! # r-horse numbers via Stirling-weighted Fubini values

This file proves the formula for `r`-horse numbers as a signed first-kind Stirling transform of
Fubini numbers.
-/


namespace MetaMathlibExt

open scoped BigOperators

def rHorse_functionSplit {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
    (Fin n → Fin k) ≃ (Fin r → Fin k) × (Fin (n - r) → Fin k) :=
  (Equiv.arrowCongr (rHorse_finSplit hrn) (Equiv.refl (Fin k))).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin r) (Fin (n - r)) (Fin k))

end MetaMathlibExt
