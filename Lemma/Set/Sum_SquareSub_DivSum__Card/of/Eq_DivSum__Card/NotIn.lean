import sympy.Basic
import Lemma.Set.EqCard.of.NotIn

open Set


@[path]
private lemma main
  [DecidableEq α]
  {a : α → ℝ}
  {X : Finset α}
  {y : α}
-- given
  (h₀ : y ∉ X)
  (h₁ : a y = (∑ x ∈ X, a x) / X.card) :
-- imply
  ∑ x ∈ X ∪ {y}, (a x - (∑ x ∈ X ∪ {y}, a x) / (X ∪ {y}).card) ^ 2 = ∑ x ∈ X, (a x - (∑ x ∈ X, a x) / X.card) ^ 2 := by
-- proof
  have h₂ : (∑ x ∈ insert y X, a x) / (X.card + 1 : ℝ) = (∑ x ∈ X, a x) / X.card := by
    rw [Finset.sum_insert h₀, h₁]
    by_cases hn : X.card = 0
    ·
      rw [Finset.card_eq_zero.mp hn]
      simp
    ·
      have hn₀ : (X.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hn₁ : (X.card : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
  rw [EqCard.of.NotIn h₀, Finset.union_singleton]
  push_cast
  rw [h₂, Finset.sum_insert h₀, ← h₁]
  simp


-- created on 2021-03-18
