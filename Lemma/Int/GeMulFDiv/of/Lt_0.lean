import Lemma.Int.FDiv.eq.Ite__Ite__Ite__Ite__Ite
import Lemma.Bool.Iff_True.of.Cond
import Lemma.Nat.Ge.is.False.of.Lt
import Lemma.Nat.Eq.is.False.of.Lt
import Lemma.Nat.Gt.is.False.of.Lt
import Lemma.Nat.Sub.eq.AddNeg
import Lemma.Int.GeMulSubDiv.of.Lt_0
import Lemma.Int.GeNeg_0.of.Le_0
import Lemma.Nat.NotGt.is.Le
import Lemma.Int.LeMulDiv.of.Ge_0
import Lemma.Int.GeNeg.of.Le_Neg
open Bool Int Nat


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
    apply GeMulSubDiv.of.Lt_0 h
  ·
    have h := Le.of.NotGt h'
    have := GeNeg_0.of.Le_0 h
    apply GeNeg.of.Le_Neg
    apply LeMulDiv.of.Ge_0 this d


-- created on 2025-03-21
-- updated on 2025-03-29
