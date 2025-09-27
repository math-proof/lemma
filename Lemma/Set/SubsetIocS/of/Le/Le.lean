import Lemma.Set.SubsetIocS.of.Le.Ge
open Set


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b a' b' : α}
-- given
  (h₀ : a' ≤ a)
  (h₁ : b ≤ b') :
-- imply
  Ioc a b ⊆ Ioc a' b' := by
-- proof
  apply SubsetIocS.of.Le.Ge <;>
    assumption



-- created on 2025-03-02
