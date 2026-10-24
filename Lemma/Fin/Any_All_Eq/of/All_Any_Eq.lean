import Mathlib
import sympy.Basic
import sympy.analysis.Misc.FiniteChoice


/--
[finite_choice](https://github.com/teorth/analysis/blob/main/Analysis/Misc/FiniteChoice.lean)
-/
@[path]
private lemma main
  {X : Type*}
  {f:X → ℕ}
  {N:ℕ}
-- given
  (h: ∀ n < N, ∃ x, f x = n) :
-- imply
  ∃ g: Fin N → X, ∀ n, f (g n) = n :=
-- proof
  finite_choice h


-- created on 2026-10-22
