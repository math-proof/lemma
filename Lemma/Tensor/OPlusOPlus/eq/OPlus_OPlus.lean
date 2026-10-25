import Notation.Algebra.BigOperators.PrefixSum.AllPrefixSums.Part4


@[path]
private lemma main
  [OPlus α]
  {a b c : α} :
-- imply
  ((a ⊕ b) ⊕ c) = a ⊕ (b ⊕ c) :=
  OPlus.associative a b c


-- created on 2024-12-08
