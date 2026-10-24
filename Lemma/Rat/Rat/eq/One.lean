import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.coe_Int_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {a:ℤ} :
-- imply
  (a:Section_4_2.Rat) = a // 1 :=
-- proof
  Section_4_2.Rat.coe_Int_eq a


-- created on 2026-10-22
