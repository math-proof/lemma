import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_379.Part2
open Nat


/--
[lemma_2](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_379.lean)
-/
@[path]
private lemma main
  {n k p r:ℕ}
-- given
  (hk: 2 ≤ k)
  (hn: k ≤ n)
  (hp: p.Prime)
  (h0: p^r ∣ n-1)
  (hr: 0 < r)
  (h1: ¬p∣k)
  (h2: ¬ p∣n-k) :
-- imply
  p^r ∣ n.choose k :=
-- proof
  lemma_2 hk hn hp h0 hr h1 h2


-- created on 2026-10-22
