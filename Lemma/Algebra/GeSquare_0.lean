import sympy.core.power
import Lemma.Basic


@[main]
private lemma main
  [Semiring α] [LinearOrder α]
  [IsRightCancelAdd α] [ZeroLEOneClass α] [ExistsAddOfLE α]
  [PosMulMono α] [AddLeftStrictMono α]
  {a : α} :
-- imply
  a² ≥ 0 :=
-- proof
  sq_nonneg a


-- created on 2024-11-29
