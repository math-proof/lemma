import Lemma.Set.Union
import Lemma.Set.UnionUnion.eq.Union_Union
open Set


@[main]
private lemma Comm
  {a b c : Set α} :
-- imply
  a ∪ b ∪ c = a ∪ c ∪ b := by
-- proof
  rw [UnionUnion.eq.Union_Union]
  rw [Union.comm (a := b)]
  rw [Union_Union.eq.UnionUnion]


-- created on 2025-07-20
