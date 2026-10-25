import Mathlib
import sympy.Basic
import Instance.Analysis.Section_2_2.Part2
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.le_refl](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {a:Chapter2.Nat} :
-- imply
  a ≤ a :=
-- proof
  a.ge_refl


-- created on 2026-10-22
-- updated on 2026-10-23
