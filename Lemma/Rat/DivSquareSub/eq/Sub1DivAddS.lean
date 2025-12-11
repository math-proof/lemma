import Lemma.Int.GeSquare_0
import Lemma.Int.SquareSub.eq.SubAddSquareS_MulMul2
import Lemma.Int.SubAddS.eq.Sub
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Rat.Sub1Div.eq.DivSub.of.Ne_0
open Int Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : α) :
-- imply
  (a - b)² / (1 + a² + b²) = 1 - (1 + 2 * a * b) / (1 + a² + b²) := by
-- proof
  rw [Sub1Div.eq.DivSub.of.Ne_0]
  ·
    apply EqDivS.of.Eq
    rw [AddAdd.eq.Add_Add]
    rw [SubAddS.eq.Sub.left]
    rw [SquareSub.eq.SubAddSquareS_MulMul2]
  ·
    have h_a := GeSquare_0 a
    have h_b := GeSquare_0 b
    linarith


-- created on 2025-12-11
