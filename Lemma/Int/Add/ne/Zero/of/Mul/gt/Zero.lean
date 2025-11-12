import Lemma.Int.GeSquare_0
import Lemma.Int.LtNeg_0.of.Gt_0
import Lemma.Int.MulNeg.eq.NegSquare
import Lemma.INt.EqSub.is.Eq_Add
import Lemma.Nat.Lt.of.Lt.Le
open Int Nat


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
