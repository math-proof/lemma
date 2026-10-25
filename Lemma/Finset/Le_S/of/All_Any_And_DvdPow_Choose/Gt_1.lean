import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_379.Part2
open Nat


/--
[S_ge](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_379.lean)
-/
@[path]
private lemma main
  {n r:ℕ}
-- given
  (hn: 1 < n)
  (h: ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p^r ∣ n.choose k) :
-- imply
  r ≤ S n :=
-- proof
  S_ge hn h


-- created on 2026-10-22
