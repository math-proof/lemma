import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_707
open Mainstep


/--
[f_second_fixed](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_707.lean)
-/
@[path]
private lemma main
  [Hypotheses]
  {a:ZMod N}
  {ha: a ∉ B}
  {b:B}
-- given
  (hb: f ha b = b) :
-- imply
  ∃ c:B, c ≠ b ∧ f ha c = c :=
-- proof
  Mainstep.f_second_fixed hb


-- created on 2026-10-22
