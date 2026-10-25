import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_379.Part2
open Nat


/--
[lemma_1](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_379.lean)
-/
@[path]
private lemma main
  {n k p a b:ℕ}
-- given
  (hk: 1 ≤ k)
  (hp: p.Prime)
  (h0: p^(a+b+1) ∣ n) :
-- imply
  p^(a+1) ∣ n.choose k ∨ p^(b+1) ∣ k :=
-- proof
  lemma_1 hk hp h0


-- created on 2026-10-22
