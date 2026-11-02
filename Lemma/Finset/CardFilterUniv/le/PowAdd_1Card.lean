import Mathlib.Data.Fintype.BigOperators
import Initialize.Tactic.Attr.Basic
open Finset


/--
There are at most `(n + 1) ^ |α|` empirical counts on a finite alphabet.
Each letter occurs at most `n` times, so a count is a function `α → Fin (n + 1)`,
and only some of those functions sum to `n`. A union over types therefore multiplies
a probability by a polynomial and does not change the exponential rate in Sanov's theorem.
-/
@[path]
private lemma main
  [Fintype α] [DecidableEq α]
-- given
  (n : ℕ) :
-- imply
  ((univ : Finset (α → Fin (n + 1))).filter (fun c => ∑ a, (c a).1 = n)).card ≤ (n + 1) ^ Fintype.card α := by
-- proof
  refine le_trans (Finset.card_le_univ _) ?_
  simp [Finset.card_univ, Fintype.card_fin]


-- created on 2026-11-02
