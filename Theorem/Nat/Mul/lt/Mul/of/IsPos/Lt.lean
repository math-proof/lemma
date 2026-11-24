module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_3.Part2
public import Theorem.Nat.EqAddMulAddMulS
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


public section

/--
[Nat.mul_lt_mul_of_pos_right](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_3.lean)
-/
@[path]
private theorem main
  {a b c: Chapter2.Nat}
-- given
  (h: a < b)
  (hc: c.IsPos) :
-- imply
  a * c < b * c :=
-- proof
  by
    rw [lt_iff_add_pos] at h
    choose d hdpos hd using h
    replace hd := congr($hd * c)
    rw [EqAddMulAddMulS] at hd
    have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
    rw [lt_iff_add_pos]
    use d * c


-- created on 2026-10-22
-- updated on 2026-10-26
