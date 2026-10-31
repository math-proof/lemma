import Notation.Fun
import Initialize.Tactic.Attr.Basic


/--
Mean-deviation sum-of-squares identity (SSE expansion):
`∑_{i ∈ s} (a i - mean)² = ∑ a i² - (∑ a i)² / |s|`
where `mean = (∑_{i ∈ s} a i) / |s|`.
Holds for the empty set as well (`0 = 0 - 0 / 0` via Mathlib `0 / 0 = 0`).

Specializes to the `Fin n` form
`∑ j, (z j - (∑ k, z k) / n)² = (∑ j, z j²) - n * ((∑ k, z k) / n)²`
by taking `s = univ`.
| attributes | lemma |
| :---: | :---: |
| path | Finset.Sum_SquareSub_DivSum.eq.Sub_DivSquareSum |
| Fun | Finset.Sum_SquareSub_DivSum.eq.Sub_DivSquareSum.fun |
-/
@[path, Fun]
private lemma main
  {s : Finset α}
  {a : α ⇀ ℝ} :
-- imply
  ∑ i ∈ s, (a[i] - (∑ i ∈ s, a[i]) / (s.card : ℝ)) ^ 2 =
    ∑ i ∈ s, a[i] ^ 2 - (∑ i ∈ s, a[i]) ^ 2 / (s.card : ℝ) := by
-- proof
  if h : s.card = 0 then
    simp [Finset.card_eq_zero.mp h]
  else
    have hc : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
    have hμ : ∑ i ∈ s, ((∑ i ∈ s, a[i]) / (s.card : ℝ)) ^ 2 =
        (∑ i ∈ s, a[i]) ^ 2 / (s.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    have hcross : ∑ i ∈ s, 2 * a[i] * ((∑ i ∈ s, a[i]) / (s.card : ℝ)) =
        2 * (∑ i ∈ s, a[i]) ^ 2 / (s.card : ℝ) := by
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      field_simp
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hμ, hcross]
    field_simp
    ring


-- created on 2026-10-31

