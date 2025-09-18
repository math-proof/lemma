import Lemma.Algebra.Eq_0.of.EqNorm_0
import Lemma.Algebra.EqAbs_0.is.Eq_0
open Algebra


@[main]
private lemma main
  [AddGroup α] [LinearOrder α] [AddLeftMono α] [AddRightMono α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  |a| ≠ 0 := by
-- proof
  by_contra h
  have := Eq_0.of.EqAbs_0 h
  contradiction


@[main]
private lemma complex
  {a : ℂ}
-- given
  (h : a ≠ 0) :
-- imply
  ‖a‖ ≠ 0 := by
-- proof
  by_contra h_Eq_0
  have := Eq_0.of.EqNorm_0 h_Eq_0
  contradiction


-- created on 2025-01-14
-- updated on 2025-08-02
