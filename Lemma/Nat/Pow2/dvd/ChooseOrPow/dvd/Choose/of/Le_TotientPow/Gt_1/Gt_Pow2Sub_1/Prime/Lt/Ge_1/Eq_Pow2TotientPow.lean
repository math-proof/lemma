import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_379.Part2
open Nat


/--
[key_prop](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_379.lean)
-/
@[path]
private lemma main
  {k n p r R:ℕ}
-- given
  (hn: n = 2^((p^R).totient))
  (hk: 1 ≤ k)
  (hkn: k < n)
  (hp: p.Prime)
  (hpr: p > 2^(r-1))
  (hr: 1 < r)
  (hr' : r ≤ (p^R).totient) :
-- imply
  2^r ∣ n.choose k ∨ p^R ∣ n.choose k :=
-- proof
  key_prop hn hk hkn hp hpr hr hr'


-- created on 2026-10-22
