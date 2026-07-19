import Lemma.Nat.Le.is.Lt.ou.Eq
import Lemma.Int.Ge_0.of.Lt_0.Le_0
open Int Nat


@[main]
private lemma main
  [Semiring α]
  [PartialOrder α]
  [ExistsAddOfLE α]
  [MulPosStrictMono α]
  [AddRightStrictMono α]
  [AddRightReflectLT α]
  {x y : α}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y ≤ 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  obtain hx | hx := Lt.ou.Eq.of.Le h₀
  ·
    apply Ge_0.of.Lt_0.Le_0 hx h₁
  ·
    simp_all


-- created on 2025-03-23
-- updated on 2026-07-19
