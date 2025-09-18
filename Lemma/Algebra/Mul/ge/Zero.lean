import Lemma.Algebra.Square.eq.Mul
import Lemma.Algebra.GeSquare_0
open Algebra


@[main]
private lemma main
  [Semiring α] [LinearOrder α]
  [IsRightCancelAdd α] [ZeroLEOneClass α] [ExistsAddOfLE α]
  [PosMulMono α] [AddLeftStrictMono α]
  {a : α} :
-- imply
  a * a ≥ 0 := by
-- proof
  rw [Mul.eq.Square]
  apply GeSquare_0


-- created on 2024-11-29
