import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_3
import Lemma.Nat.Mul.lt.Mul.of.IsPos.Lt
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.mul_gt_mul_of_pos_right](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private lemma main
  {a b c: Chapter2.Nat}
-- given
  (h: a > b)
  (hc: c.IsPos) :
-- imply
  a * c > b * c :=
-- proof
  Mul.lt.Mul.of.IsPos.Lt h hc


-- created on 2026-10-22
-- updated on 2026-10-23
