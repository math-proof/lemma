import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_379
open Nat


/--
[key_cor](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_379.lean)
-/
@[path]
private lemma main
  {p r:ℕ}
-- given
  (hp: p.Prime)
  (hpr: p > 2^(r-1))
  (hr: 1 < r) :
-- imply
  r ≤ S (2^((p^r).totient)) :=
-- proof
  key_cor hp hpr hr


-- created on 2026-10-22
