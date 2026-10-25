import Mathlib
import sympy.Basic
import Instance.Analysis.Section_2_3.Part2
import Lemma.Nat.PowNat.eq.MulPow
import Lemma.Nat.Pow_0.eq.One
import Lemma.Nat.Eq1Mul
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.pow_one](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private lemma main
  {m: Chapter2.Nat} :
-- imply
  m ^ (1:Chapter2.Nat) = m :=
-- proof
  by
    rw [← zero_succ, PowNat.eq.MulPow, Pow_0.eq.One, Eq1Mul]


-- created on 2026-10-22
-- updated on 2026-10-23
