import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma int
  [IntegerRing Z]
-- given
  (a : Z) :
-- imply
  a - a = 0 :=
-- proof
  IntegerRing.sub_self a


/--
In any additive group `α`, subtracting an element `a` from itself yields the additive identity `0`.
This fundamental property, expressed as `a - a = 0`, is essential for simplifying expressions and streamlining proofs involving group operations.
-/
@[main]
private lemma main
  [AddGroup α]
  {a : α} :
-- imply
  a - a = 0 :=
-- proof
  sub_self a


-- created on 2024-07-01
-- updated on 2025-07-11
