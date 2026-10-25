import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.LUB_claim2](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {E : Set Chapter5.Real}
  {N:ℕ}
  {a b: ℕ → ℚ}
-- given
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E) :
-- imply
  ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) :=
-- proof
  Chapter5.Real.LUB_claim2 N hb hm1 hm2


-- created on 2026-10-22
