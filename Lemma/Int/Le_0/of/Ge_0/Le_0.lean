import Lemma.Nat.Eq.ou.Lt.of.Le
import Lemma.Int.Le_0.of.Ge_0.Lt_0
open Int Nat


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [PosMulStrictMono α]
  {x y : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y ≤ 0) :
-- imply
  x * y ≤ 0 := by
-- proof
  obtain hy | hy' := Eq.ou.Lt.of.Le h₁
  ·
    simp_all
  ·
    apply Le_0.of.Ge_0.Lt_0 h₀ hy'


-- created on 2025-03-23
-- updated on 2025-04-04
