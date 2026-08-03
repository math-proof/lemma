import Lemma.Int.GeSquare_0
import Lemma.Nat.SquareAdd.eq.AddAddSquareS_MulMul2
open Nat Int


@[main]
private lemma main
  [CommSemiring α] [LinearOrder α] [ExistsAddOfLE α] [PosMulMono α] [AddLeftMono α]
  {x y : α} :
-- imply
  x² + y² + 2 * x * y ≥ 0 := by
-- proof
  rw [AddAddSquareS_MulMul2.eq.SquareAdd]
  apply GeSquare_0


-- created on 2026-08-03
