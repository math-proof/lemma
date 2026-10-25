import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_8_1.Part4
open Chapter8
open Chapter8.Nat hiding min


/--
[Nat.min_spec](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  {X : Set ℕ}
-- given
  (hX : X.Nonempty) :
-- imply
  Chapter8.Nat.min X ∈ X ∧ ∀ n ∈ X, Chapter8.Nat.min X ≤ n :=
-- proof
  Chapter8.Nat.min_spec hX


-- created on 2026-10-22
