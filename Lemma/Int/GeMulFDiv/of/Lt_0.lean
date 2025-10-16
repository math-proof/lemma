import Lemma.Int.FDiv.eq.Ite__Ite__Ite__Ite__Ite
import Lemma.Bool.Iff_True.of.Cond
import Lemma.Nat.Ge.is.False.of.Lt
import Lemma.Algebra.Eq.is.False.of.Lt
import Lemma.Algebra.Gt.is.False.of.Lt
import Lemma.Algebra.Sub.eq.AddNeg
import Lemma.Int.GeMulSubEDiv.of.Lt_0
import Lemma.Algebra.GeNeg_0.of.Le_0
import Lemma.Algebra.NotGt.is.Le
import Lemma.Algebra.LeMulEDiv.of.Ge_0
import Lemma.Algebra.GeNeg.of.Le_Neg
open Algebra Bool Int Nat


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d < 0)
  (n : ℤ) :
-- imply
  n // d * d ≥ n := by
-- proof
  rw [FDiv.eq.Ite__Ite__Ite__Ite__Ite]
  have := Iff_True.of.Cond h
  simp [this]
  have := Ge.is.False.of.Lt h
  simp [this]
  have := Eq.is.False.of.Lt h
  simp [this]
  have := Gt.is.False.of.Lt h
  simp [this]
  split_ifs with h'
  ·
    rw [AddNeg.eq.Sub]
    apply GeMulSubEDiv.of.Lt_0 h
  ·
    have h := Le.of.NotGt h'
    have := GeNeg_0.of.Le_0 h
    apply GeNeg.of.Le_Neg
    apply LeMulEDiv.of.Ge_0 this d


-- created on 2025-03-21
-- updated on 2025-03-29
