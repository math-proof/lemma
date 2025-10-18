import Lemma.Int.EqSub.of.EqAdd
import Lemma.Algebra.NegMul.eq.MulNeg
import Lemma.Algebra.MulNeg.eq.NegSquare
import Lemma.Algebra.LtNeg_0.of.Gt_0
import Lemma.Algebra.GeSquare_0
import Lemma.Nat.Lt.of.Lt.Le
open Algebra Int Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h : a * b > 0) :
-- imply
  a + b ≠ 0 := by
-- proof
  by_contra h'
  have h' := Eq_Sub.of.EqAdd h'
  simp at h'
  rw [h'] at h
  rw [MulNeg.eq.NegSquare] at h
  have h := LtNeg_0.of.Gt_0 h
  simp at h
  have h := Lt.of.Lt.Le h (GeSquare_0 (a := b))
  simp at h


-- created on 2024-11-29
