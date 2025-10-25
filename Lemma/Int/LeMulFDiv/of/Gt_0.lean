import Lemma.Int.FDiv.eq.Ite__Ite__Ite__Ite__Ite
import Lemma.Bool.Iff_True.of.Cond
import Lemma.Algebra.Lt.is.False.of.Gt
import Lemma.Nat.Ge.is.True.of.Gt
import Lemma.Nat.Eq.is.False.of.Gt
import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Algebra.LeMulEDiv.of.Ge_0
import Lemma.Algebra.NegAdd.eq.SubNeg
import Lemma.Int.NegMul.eq.MulNeg
import Lemma.Int.LeNeg.of.Ge_Neg
import Lemma.Int.GtNeg_0.of.Lt_0
import Lemma.Int.GeMulAdd1EDiv.of.Gt_0
open Algebra Bool Int Nat


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d > 0)
  (n : ℤ) :
-- imply
  n // d * d ≤ n := by
-- proof
  rw [FDiv.eq.Ite__Ite__Ite__Ite__Ite]
  have := Iff_True.of.Cond h
  simp [this]
  have := Lt.is.False.of.Gt h
  simp [this]
  have := Ge.is.True.of.Gt h
  simp [this]
  have := Eq.is.False.of.Gt h
  simp [this]
  rw [Add_Neg.eq.Sub]
  split_ifs with h' h''
  ·
    apply LeMulEDiv.of.Ge_0 h' d
  ·
    rw [SubNeg.eq.NegAdd]
    rw [MulNeg.eq.NegMul]
    apply LeNeg.of.Ge_Neg
    apply GeMulAdd1EDiv.of.Gt_0 h
  ·
    linarith [h', h'']


-- created on 2025-03-29
