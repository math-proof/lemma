import Lemma.Basic


@[main, comm]
private lemma main
  [LinearOrderedRing α]
-- given
  (a b : α) :
-- imply
  |a * b| = |a| * |b| :=
  -- proof
  abs_mul a b


-- created on 2025-04-19
