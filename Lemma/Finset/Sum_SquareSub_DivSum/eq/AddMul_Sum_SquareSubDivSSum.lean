import Mathlib.Tactic
import Notation.Fun
import Initialize.Tactic.Attr.Basic


/--
One-way ANOVA sum-of-squares identity: `ST = SB + SW`
(total = between-row + within-row).

For an `m × n` array `x : ℕ ⇀ ℕ ⇀ R` (notebook notation `Υ`), including the
`n = 0` case (empty column range; Mathlib `/ 0 = 0`):
* grand mean `μ = (∑ᵢ ∑ⱼ x[i][j]) / (m * n)`
* row mean `ȳᵢ = (∑ⱼ x[i][j]) / n`
* `ST = ∑ᵢ ∑ⱼ (x[i][j] - μ)²`  (total)
* `SB = n * ∑ᵢ (ȳᵢ - μ)²`    (between-row / SSB)
* `SW = ∑ᵢ ∑ⱼ (x[i][j] - ȳᵢ)²`  (within-row / SSW)

So `ST = SB + SW`.
-/
@[path]
private lemma main
  [Field R]
  {m n : ℕ}
  {x : ℕ ⇀ ℕ ⇀ R} :
-- imply
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (x[i][j] - (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, x[i][j]) / (m * n)) ^ 2 =
      n * ∑ i ∈ Finset.range m, ((∑ j ∈ Finset.range n, x[i][j]) / n - (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, x[i][j]) / (m * n)) ^ 2 +
        ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (x[i][j] - (∑ j ∈ Finset.range n, x[i][j]) / n) ^ 2 := by
-- proof
  obtain hn | hn := eq_or_ne (n : R) 0
  · -- `(n : R) = 0`: means vanish by `div_zero`; `SB = 0`; `ST = SW`
    simp [hn, mul_zero, div_zero]
  · -- `(n : R) ≠ 0`
    have row : ∀ (y : ℕ ⇀ R) (c : R), ∑ j ∈ Finset.range n, (y[j] - c) ^ 2 =
        n * ((∑ j ∈ Finset.range n, y[j]) / n - c) ^ 2 + ∑ j ∈ Finset.range n, (y[j] - (∑ j ∈ Finset.range n, y[j]) / n) ^ 2 := by
      intro y c
      have key : ∀ d : R, ∑ j ∈ Finset.range n, (y[j] - d) ^ 2 = ∑ j ∈ Finset.range n, y[j] ^ 2 - 2 * d * ∑ j ∈ Finset.range n, y[j] + n * d ^ 2 := by
        intro d
        have e : ∀ j : ℕ, (y[j] - d) ^ 2 = y[j] ^ 2 - 2 * d * y[j] + d ^ 2 := fun j => by ring
        rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [key c, key]
      field_simp
      ring
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact row x[i] _


-- created on 2020-03-27
-- updated on 2026-10-30
