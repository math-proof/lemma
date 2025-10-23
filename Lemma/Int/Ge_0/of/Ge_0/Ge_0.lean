import Lemma.Nat.Eq.ou.Gt.of.Ge
import Lemma.Int.Ge_0.of.Gt_0.Ge_0
open Nat Int


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [PosMulStrictMono α]
  {x y : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y ≥ 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  obtain hx | hx := Eq.ou.Gt.of.Ge h₀
  ·
    simp_all
  ·
    apply Ge_0.of.Gt_0.Ge_0 hx h₁


-- created on 2025-03-23
