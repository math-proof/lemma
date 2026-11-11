import Notation.Algebra.BigOperators.PrefixSum.AllPrefixSums.Part4


@[path]
private lemma main
  [OPlus α]
  [Std.Associative (α := α) OPlus.oplus]
  {a b c : α} :
-- imply
  ((a ⊕ b) ⊕ c) = a ⊕ (b ⊕ c) :=
  Std.Associative.assoc a b c


-- created on 2024-12-08
