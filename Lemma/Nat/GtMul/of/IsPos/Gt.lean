import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_2_3.Part2
import Lemma.Nat.LtMul.of.IsPos.Lt
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.mul_gt_mul_of_pos_left](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private lemma main
  {a b c: Chapter2.Nat}
-- given
  (h: a > b)
  (hc: c.IsPos) :
-- imply
  c * a > c * b :=
-- proof
  LtMul.of.IsPos.Lt h hc


-- created on 2026-10-22
-- updated on 2026-10-26
