import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_3
import Lemma.Nat.MulAddEqAddMulS
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private lemma main
  {a b c: Chapter2.Nat} :
-- imply
  (a + b)*c = a*c + b*c :=
-- proof
  by
    simp only [mul_comm, MulAddEqAddMulS]


-- created on 2026-10-22
-- updated on 2026-10-23
