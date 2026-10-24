import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.coe_Nat_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {n:ℕ} :
-- imply
  (n:Section_4_2.Rat) = n // 1 :=
-- proof
  Section_4_2.Rat.coe_Nat_eq n


-- created on 2026-10-22
