import Lemma.Nat.Le.is.Lt.ou.Eq
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
  obtain hy | hy' := Eq.ou.Lt.of.Ge h₁
  ·
    aesop
  ·
    apply Le_0.of.Ge_0.Lt_0 h₀ hy'


-- created on 2018-02-10
-- updated on 2025-04-04
