import Lemma.Int.GeSquare_0
import Lemma.Nat.Square.eq.Mul
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
open Int Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a² ≠ 0 := by
-- proof
  by_contra h'
  rw [Square.eq.Mul] at h'
  have h := OrEqS_0.of.Mul.eq.Zero h'
  simp at h
  contradiction


-- created on 2024-11-29
