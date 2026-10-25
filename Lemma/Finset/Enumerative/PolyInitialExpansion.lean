import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.GeneralizedStirlingNumbers
import Lemma.Finset.Enumerative.GeneralizedStirlingNumbers


namespace MetaMathlibExt

/--
[polyInitialExpansion_stirlingSecond_sum_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PolyInitialExpansion.lean)
-/
@[path]
private lemma polyInitialExpansion_stirlingSecond_sum_succ (t : ℕ) (b : ℕ → ℝ) :
  ∑ m ∈ Finset.range (t + 1),
    (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) * (Nat.stirlingSecond t m : ℝ) *
      ((m : ℝ) * b m - ((m : ℝ) + 1) * b (m + 1)) =
    ∑ m ∈ Finset.range (t + 2),
      (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (Nat.stirlingSecond (t + 1) m : ℝ) * b m := by
  have hshift :
    (∑ m ∈ Finset.range (t + 1),
      (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) * (Nat.stirlingSecond t m : ℝ) *
        ((m : ℝ) * b m)) =
      ∑ m ∈ Finset.range (t + 1),
        (-1 : ℝ) ^ (m + 1) * (Nat.factorial (m + 1) : ℝ) *
          (Nat.stirlingSecond t (m + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) * b (m + 1) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self t), Nat.cast_zero,
      mul_zero, zero_mul, add_zero]
    ring_nf
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [hshift, ← Finset.sum_sub_distrib]
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Nat.factorial_succ, Nat.stirlingSecond_succ_succ, pow_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[chen_stirlingSecond_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PolyInitialExpansion.lean)
-/
@[path]
lemma chen_stirlingSecond_expansion
  {t : ℕ} :
-- imply
  ∀ (a : ℕ → ℕ → ℝ),
    (∀ (m s : ℕ),
    a m (s + 1) = (m : ℝ) * a m s - ((m : ℝ) + 1) * a (m + 1) s) →
    a 0 t = ∑ m ∈ Finset.range (t + 1),
    (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
    (Nat.stirlingSecond t m : ℝ) * a m 0 := by
-- proof
  induction t with
  | zero =>
    intro a hrec
    simp
  | succ t ih =>
    intro a hrec
    have hshift : ∀ (m s : ℕ),
      a m (s + 1 + 1) =
        (m : ℝ) * a m (s + 1) - ((m : ℝ) + 1) * a (m + 1) (s + 1) := by
      intro m s
      exact hrec m (s + 1)
    calc
      a 0 (t + 1) =
        ∑ m ∈ Finset.range (t + 1),
          (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
            (Nat.stirlingSecond t m : ℝ) * a m 1 := by
        simpa using ih (fun m s ↦ a m (s + 1)) hshift
      _ = ∑ m ∈ Finset.range (t + 1),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          (Nat.stirlingSecond t m : ℝ) *
            ((m : ℝ) * a m 0 - ((m : ℝ) + 1) * a (m + 1) 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [hrec m 0]
      _ = ∑ m ∈ Finset.range (t + 2),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          (Nat.stirlingSecond (t + 1) m : ℝ) * a m 0 :=
        polyInitialExpansion_stirlingSecond_sum_succ t (fun m ↦ a m 0)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[polyInitialExpansion_generalizedStirlingSecond_full_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PolyInitialExpansion.lean)
-/
@[path]
private lemma polyInitialExpansion_generalizedStirlingSecond_full_range
  (n m : ℕ) (x : ℝ) :
  generalizedStirlingSecond n m x =
    ∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i := by
  unfold generalizedStirlingSecond
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hnot
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_range, not_lt] at hnot
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : n - i < m)]
    simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[polyInitialExpansion_zero_full_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PolyInitialExpansion.lean)
-/
@[path]
private lemma polyInitialExpansion_zero_full_range (n t : ℕ) (ht : t ≤ n)
  (a : ℕ → ℕ → ℝ)
  (hrec : ∀ (m s : ℕ),
    a m (s + 1) = (m : ℝ) * a m s - ((m : ℝ) + 1) * a (m + 1) s) :
  ∑ m ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
      (Nat.stirlingSecond t m : ℝ) * a m 0 = a 0 t := by
  symm
  calc
    a 0 t = ∑ m ∈ Finset.range (t + 1),
      (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (Nat.stirlingSecond t m : ℝ) * a m 0 :=
      chen_stirlingSecond_expansion t a hrec
    _ = ∑ m ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (Nat.stirlingSecond t m : ℝ) * a m 0 := by
      apply Finset.sum_subset
      · intro m hm
        simp only [Finset.mem_range] at hm ⊢
        omega
      · intro m hm hnot
        simp only [Finset.mem_range] at hm
        simp only [Finset.mem_range, not_lt] at hnot
        rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : t < m)]
        simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[poly_initial_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PolyInitialExpansion.lean)
-/
@[path]
lemma poly_initial_expansion
  :
-- imply
  ∀ (n : ℕ) (x : ℝ) (a : ℕ → ℕ → ℝ)
    (hrec : ∀ (m t : ℕ),
    a m (t + 1) = (m : ℝ) * a m t - ((m : ℝ) + 1) * a (m + 1) t),
    ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * x ^ k * a 0 (n - k) =
    ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
    (generalizedStirlingSecond n m x) * a m 0 := by
-- proof
  intro n x a hrec
  symm
  calc
    (∑ m ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (generalizedStirlingSecond n m x) * a m 0) =
      ∑ m ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          (∑ i ∈ Finset.range (n + 1),
            (Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i) *
          a m 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [polyInitialExpansion_generalizedStirlingSecond_full_range]
    _ = ∑ m ∈ Finset.range (n + 1),
      ∑ i ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          ((Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i) *
          a m 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i ∈ Finset.range (n + 1),
      ∑ m ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          ((Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i) *
          a m 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℝ) * x ^ i *
        (∑ m ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
            (Nat.stirlingSecond (n - i) m : ℝ) * a m 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = ∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℝ) * x ^ i * a 0 (n - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [polyInitialExpansion_zero_full_range n (n - i) (Nat.sub_le n i) a hrec]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
