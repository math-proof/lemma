import Notation.Algebra.BigOperators.PrefixSum.AllPrefixSums.Part4


@[path]
private lemma main
  [OPlus α]
  [OTimes α]
  [ODot α]
  {a b c : α} :
-- imply
  (a ⊙ b) ⊙ c = a ⊙ (b ⊙ c) :=
  ODot.associative a b c


-- created on 2024-12-08
