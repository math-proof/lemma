import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  [Semiring α] [LinearOrder α] [ExistsAddOfLE α] [PosMulMono α] [AddLeftMono α]
-- given
  (a : α) :
-- imply
  a² ≥ 0 :=
-- proof
  sq_nonneg a


-- created on 2024-11-29
