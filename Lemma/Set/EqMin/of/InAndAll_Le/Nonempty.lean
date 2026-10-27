import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_1.Part4
open Chapter8
open Chapter8.Nat hiding min


/--
[Nat.min_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  {X : Set ℕ}
  {a:ℕ}
-- given
  (hX : X.Nonempty)
  (ha : a ∈ X ∧ ∀ n ∈ X, a ≤ n) :
-- imply
  Chapter8.Nat.min X = a :=
-- proof
  Chapter8.Nat.min_eq hX ha


-- created on 2026-10-22
