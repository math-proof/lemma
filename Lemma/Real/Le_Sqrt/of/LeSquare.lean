import Lemma.Real.GeSqrt_0
import Lemma.Int.GeSquare_0
import Lemma.Nat.Ge.of.Ge.Ge
import Lemma.Nat.Eq.of.Le.Le
import Lemma.Int.Eq_0.of.LeSquare_0
import Lemma.Real.Le_Sqrt.is.LeSquare.of.Ge_0.Ge_0
open Nat Int Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x² ≤ y) :
-- imply
  x ≤ √y := by
-- proof
  obtain hx | hx := le_total 0 x
  ·
    obtain hy | hy := le_total 0 y
    ·
      apply Le_Sqrt.of.LeSquare.Ge_0.Ge_0
      repeat assumption
    ·
      have := GeSquare_0 (a := x)
      have := Ge.of.Ge.Ge h this
      have := Eq.of.Le.Le hy this
      rw [this]
      rw [this] at h
      norm_num
      have := Eq_0.of.LeSquare_0 h
      linarith
  ·
    have := GeSqrt_0 (x := y)
    linarith


-- created on 2025-04-06
-- updated on 2025-08-02
