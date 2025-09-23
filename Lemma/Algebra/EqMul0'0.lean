import Lemma.Basic


@[main]
private lemma main
  [MulZeroClass α]
  {a : α} :
-- imply
  0 * a = 0 := by
-- proof
  apply MulZeroClass.zero_mul


-- created on 2024-11-25
