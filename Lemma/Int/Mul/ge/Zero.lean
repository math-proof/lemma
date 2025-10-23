import Lemma.Algebra.Square.eq.Mul
import Lemma.Int.GeSquare_0
open Algebra Int


@[main]
private lemma main
  [Semiring α] [LinearOrder α] [ExistsAddOfLE α] [PosMulMono α] [AddLeftMono α]
  {a : α} :
-- imply
  a * a ≥ 0 := by
-- proof
  rw [Mul.eq.Square]
  apply GeSquare_0


-- created on 2024-11-29
