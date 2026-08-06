import Lemma.Finset.SumSetOf.eq.Sum_UFnAddMul
open Finset


@[main]
private lemma main
  [AddCommMonoid α]
  {a : ℤ}
-- given
  (ha : a ≠ 0)
  (s : Finset ℤ)
  (h : ℤ → ℝ)
  (f : ℤ → α) :
-- imply
  ∑ m ∈ {n ∈ s | h n > 0}.image (a * ·), f m = ∑ n ∈ {n ∈ s | h n > 0}, f (a * n) := by
-- proof
  simpa using SumSetOf.eq.Sum_UFnAddMul (α := α) (a := a) (b := 0) ha s h f


-- created on 2018-05-01
-- updated on 2026-08-06
