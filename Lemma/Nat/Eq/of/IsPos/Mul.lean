import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_3
import Lemma.Nat.Mul.lt.Mul.of.IsPos.Lt
import Lemma.Nat.Mul.gt.Mul.of.IsPos.Gt
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.mul_cancel_right](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private lemma main
  {a b c: Chapter2.Nat}
-- given
  (h: a * c = b * c)
  (hc: c.IsPos) :
-- imply
  a = b :=
-- proof
  by
    have := trichotomous a b
    obtain hlt | rfl | hgt := this
    ·
      replace hlt := Mul.lt.Mul.of.IsPos.Lt hlt hc
      apply Chapter2.Nat.ne_of_lt at hlt
      contradiction
    · rfl
    replace hgt := Mul.gt.Mul.of.IsPos.Gt hgt hc
    apply Chapter2.Nat.ne_of_gt at hgt
    contradiction


-- created on 2026-10-22
-- updated on 2026-10-23
