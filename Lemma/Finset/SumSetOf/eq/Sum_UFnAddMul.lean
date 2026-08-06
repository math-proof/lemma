import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lemma.Nat.Mul.is.Eq.of.Ne_0
open Nat


@[main]
private lemma main
  [AddCommMonoid α]
  {a b : ℤ}
-- given
  (ha : a ≠ 0)
  (s : Finset ℤ)
  (h : ℤ → ℝ)
  (f : ℤ → α) :
-- imply
  ∑ m ∈ {n ∈ s | h n > 0}.image (a * · + b), f m = ∑ n ∈ {n ∈ s | h n > 0}, f (a * n + b) := by
-- proof
  rw [Finset.sum_image]
  intro n₁ _ n₂ _ heq
  exact Eq.of.Mul.Ne_0 ha (by linarith : a * n₁ = a * n₂)


-- created on 2018-05-02
-- updated on 2026-08-06
