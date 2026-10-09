import sympy.sets.sets
import sympy.Basic


@[path]
private lemma doit
  [CommMonoid α]
  {x : ℕ → α} :
-- imply
  ∏ i ∈ Finset.range 5, x i = x 0 * x 1 * x 2 * x 3 * x 4 := by
-- proof
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]


@[path]
private lemma doit.outer
  [CommMonoid α]
  {f : ℕ → ℕ}
  {x : ℕ → ℕ → α} :
-- imply
  ∏ i ∈ Finset.range 5, ∏ j ∈ Finset.range (f i), x i j = (∏ j ∈ Finset.range (f 0), x 0 j) * (∏ j ∈ Finset.range (f 1), x 1 j) * (∏ j ∈ Finset.range (f 2), x 2 j) * (∏ j ∈ Finset.range (f 3), x 3 j) * (∏ j ∈ Finset.range (f 4), x 4 j) := by
-- proof
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]


@[path]
private lemma doit.outer.setlimit
  [CommMonoid α]
  {f : ℕ → ℕ}
  {x : ℕ → ℕ → α} :
-- imply
  ∏ i ∈ ({0, 1, 2, 3, 4} : Finset ℕ), ∏ j ∈ Finset.range (f i), x i j = (∏ j ∈ Finset.range (f 0), x 0 j) * (∏ j ∈ Finset.range (f 1), x 1 j) * (∏ j ∈ Finset.range (f 2), x 2 j) * (∏ j ∈ Finset.range (f 3), x 3 j) * (∏ j ∈ Finset.range (f 4), x 4 j) := by
-- proof
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
  simp only [mul_assoc]


@[path]
private lemma doit.setlimit
  [CommMonoid α]
  {x : ℕ → α} :
-- imply
  ∏ i ∈ ({0, 1, 2, 3, 4} : Finset ℕ), x i = x 0 * x 1 * x 2 * x 3 * x 4 := by
-- proof
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
  simp only [mul_assoc]


@[path]
private lemma pop
  [CommMonoid α]
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  ∏ i ∈ Finset.range (n + 1), f i = (∏ i ∈ Finset.range n, f i) * f n := by
-- proof
  exact Finset.prod_range_succ _ _


@[path]
private lemma push
  {n : ℕ}
  {f : ℕ → ℝ}
-- given
  (h : f n ≠ 0) :
-- imply
  ∏ i ∈ Finset.range n, f i = (∏ i ∈ Finset.range (n + 1), f i) / f n := by
-- proof
  rw [Finset.prod_range_succ, mul_div_assoc, div_self h, mul_one]


@[path]
private lemma scale
  {n : ℕ}
  {f : ℕ → ℝ}
  {s : ℝ}
-- given
  (h : s ≠ 0) :
-- imply
  ∏ i ∈ Finset.range n, f i = (∏ i ∈ Finset.range n, f i * s) / s ^ n := by
-- proof
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, mul_div_assoc, div_self (pow_ne_zero n h), mul_one]


@[path]
private lemma shift
  [CommMonoid α]
  {n : ℕ}
  {f : ℕ → α} :
-- imply
  ∏ i ∈ Finset.range (n + 1), f i = (∏ i ∈ Finset.Ico 1 (n + 1), f i) * f 0 := by
-- proof
  rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot (by omega), mul_comm]


@[path]
private lemma unshift
  {n : ℕ}
  {f : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h₁ : f 0 ≠ 0) :
-- imply
  ∏ i ∈ Finset.Ico 1 n, f i = (∏ i ∈ Finset.Ico 0 n, f i) * (f 0)⁻¹ := by
-- proof
  rw [Finset.prod_eq_prod_Ico_succ_bot h₀, mul_comm (f 0), mul_assoc, mul_inv_cancel₀ h₁, mul_one]


-- created on 2023-03-22
