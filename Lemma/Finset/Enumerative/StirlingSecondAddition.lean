import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[inner_Icc_eq_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondAddition.lean)
-/
@[path]
private lemma inner_Icc_eq_range (n k' v : ℕ) :
  ∑ m ∈ Finset.Icc k' v, Nat.choose v m * Nat.stirlingSecond m k' * n ^ (v - m) =
  ∑ m ∈ Finset.range (v + 1), Nat.choose v m * Nat.stirlingSecond m k' * n ^ (v - m) := by
  apply Finset.sum_subset
  · intro m hm
    simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢
    omega
  · intro m hm hnm
    simp only [Finset.mem_range] at hm
    rw [Finset.mem_Icc] at hnm
    have hlt : m < k' := by
      by_contra hcon
      exact hnm ⟨Nat.le_of_not_lt hcon, by omega⟩
    rw [Nat.stirlingSecond_eq_zero_of_lt hlt, mul_zero, zero_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[outer_Icc_eq_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondAddition.lean)
-/
@[path]
private lemma outer_Icc_eq_range (u k : ℕ) (hu : 0 < u) (f : ℕ → ℕ) :
  ∑ n ∈ Finset.Icc 1 k, Nat.stirlingSecond u n * f n =
  ∑ n ∈ Finset.range (k + 1), Nat.stirlingSecond u n * f n := by
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  · intro n hn hnn
    simp only [Finset.mem_range] at hn
    rw [Finset.mem_Icc] at hnn
    have hn0 : n = 0 := by
      by_contra hcon
      have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hcon
      exact hnn ⟨h1, by omega⟩
    subst hn0
    obtain ⟨u', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
    rw [Nat.stirlingSecond_succ_zero, zero_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[inner_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondAddition.lean)
-/
@[path]
private lemma inner_succ (n K v : ℕ) :
  ∑ m ∈ Finset.range (v + 1 + 1),
    Nat.choose (v + 1) m * Nat.stirlingSecond m (K + 1) * n ^ (v + 1 - m) =
  (n + (K + 1)) * ∑ m ∈ Finset.range (v + 1),
    Nat.choose v m * Nat.stirlingSecond m (K + 1) * n ^ (v - m) +
  ∑ m ∈ Finset.range (v + 1), Nat.choose v m * Nat.stirlingSecond m K * n ^ (v - m) := by
  have hS0 : Nat.stirlingSecond 0 (K + 1) = 0 := Nat.stirlingSecond_zero_succ K
  have hCtop : Nat.choose v (v + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self v)
  have hpeel : ∑ m ∈ Finset.range (v + 1 + 1),
    Nat.choose (v + 1) m * Nat.stirlingSecond m (K + 1) * n ^ (v + 1 - m) =
    ∑ j ∈ Finset.range (v + 1),
      Nat.choose (v + 1) (j + 1) * Nat.stirlingSecond (j + 1) (K + 1) * n ^ (v - j) := by
    rw [Finset.sum_range_succ' _ (v + 1)]
    simp only [hS0, mul_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    have e : v + 1 - (j + 1) = v - j := by omega
    rw [e]
  rw [hpeel]
  have hsplit : ∀ j ∈ Finset.range (v + 1),
    Nat.choose (v + 1) (j + 1) * Nat.stirlingSecond (j + 1) (K + 1) * n ^ (v - j) =
    (Nat.choose v j * Nat.stirlingSecond (j + 1) (K + 1) * n ^ (v - j)) +
    (Nat.choose v (j + 1) * Nat.stirlingSecond (j + 1) (K + 1) * n ^ (v - j)) := by
    intro j _
    rw [Nat.choose_succ_succ v j, add_mul, add_mul]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hA : ∑ j ∈ Finset.range (v + 1),
    Nat.choose v j * Nat.stirlingSecond (j + 1) (K + 1) * n ^ (v - j) =
    (K + 1) * ∑ m ∈ Finset.range (v + 1),
      Nat.choose v m * Nat.stirlingSecond m (K + 1) * n ^ (v - m) +
    ∑ m ∈ Finset.range (v + 1), Nat.choose v m * Nat.stirlingSecond m K * n ^ (v - m) := by
    have hterm : ∀ j ∈ Finset.range (v + 1),
      Nat.choose v j * Nat.stirlingSecond (j + 1) (K + 1) * n ^ (v - j) =
      ((K + 1) * (Nat.choose v j * Nat.stirlingSecond j (K + 1) * n ^ (v - j))) +
      (Nat.choose v j * Nat.stirlingSecond j K * n ^ (v - j)) := by
      intro j _
      rw [Nat.stirlingSecond_succ_succ j K]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hB : ∑ j ∈ Finset.range (v + 1),
    Nat.choose v (j + 1) * Nat.stirlingSecond (j + 1) (K + 1) * n ^ (v - j) =
    n * ∑ m ∈ Finset.range (v + 1),
      Nat.choose v m * Nat.stirlingSecond m (K + 1) * n ^ (v - m) := by
    have hT : ∑ m ∈ Finset.range (v + 1 + 1),
      Nat.choose v m * Nat.stirlingSecond m (K + 1) * n ^ (v + 1 - m) =
      ∑ j ∈ Finset.range (v + 1),
        Nat.choose v (j + 1) * Nat.stirlingSecond (j + 1) (K + 1) * n ^ (v - j) := by
      rw [Finset.sum_range_succ' _ (v + 1)]
      simp only [hS0, mul_zero, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      have e : v + 1 - (j + 1) = v - j := by omega
      rw [e]
    rw [← hT]
    rw [Finset.sum_range_succ _ (v + 1)]
    simp only [hCtop, zero_mul, add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_range] at hm
    have e : v + 1 - m = (v - m) + 1 := by omega
    rw [e, pow_succ]
    ring
  rw [hA, hB]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[inner_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondAddition.lean)
-/
@[path]
private lemma inner_zero (n v : ℕ) :
  ∑ m ∈ Finset.range (v + 1), Nat.choose v m * Nat.stirlingSecond m 0 * n ^ (v - m) = n ^ v := by
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.stirlingSecond_zero, one_mul, Nat.sub_zero, mul_one]
  · intro b _ hb0
    obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
    rw [Nat.stirlingSecond_succ_zero, mul_zero, zero_mul]
  · simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[inner_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondAddition.lean)
-/
@[path]
private lemma inner_zero_succ (n v : ℕ) :
  ∑ m ∈ Finset.range (v + 1 + 1),
    Nat.choose (v + 1) m * Nat.stirlingSecond m 0 * n ^ (v + 1 - m) =
  n * ∑ m ∈ Finset.range (v + 1), Nat.choose v m * Nat.stirlingSecond m 0 * n ^ (v - m) := by
  rw [inner_zero n (v + 1), inner_zero n v, pow_succ']

end MetaMathlibExt

namespace MetaMathlibExt

/--
[inner_one_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondAddition.lean)
-/
@[path]
private lemma inner_one_zero (n k' : ℕ) :
  (∑ m ∈ Finset.range 1, Nat.choose 0 m * Nat.stirlingSecond m k' * n ^ (0 - m)) =
  Nat.stirlingSecond 0 k' := by
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero, pow_zero, mul_one]
  · intro b hb hb0
    simp only [Finset.mem_range] at hb
    exact absurd (Nat.lt_one_iff.mp hb) hb0
  · intro hcon
    exact absurd (Finset.mem_range.mpr (by omega : (0 : ℕ) < 1)) hcon

end MetaMathlibExt

namespace MetaMathlibExt

/--
[stirlingSecond_addition_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondAddition.lean)
-/
@[path]
private lemma stirlingSecond_addition_range (u v : ℕ) (hu : 0 < u) (k : ℕ) :
  Nat.stirlingSecond (u + v) k =
  ∑ n ∈ Finset.range (k + 1), Nat.stirlingSecond u n *
    ∑ m ∈ Finset.range (v + 1), Nat.choose v m * Nat.stirlingSecond m (k - n) * n ^ (v - m) := by
  induction v generalizing k with
  | zero =>
    change Nat.stirlingSecond u k =
      ∑ n ∈ Finset.range (k + 1), Nat.stirlingSecond u n *
      ∑ m ∈ Finset.range 1, Nat.choose 0 m * Nat.stirlingSecond m (k - n) * n ^ (0 - m)
    have hG : ∀ n ∈ Finset.range (k + 1),
      Nat.stirlingSecond u n *
      (∑ m ∈ Finset.range 1, Nat.choose 0 m * Nat.stirlingSecond m (k - n) * n ^ (0 - m)) =
      Nat.stirlingSecond u n * Nat.stirlingSecond 0 (k - n) := by
      intro n _
      rw [inner_one_zero]
    rw [Finset.sum_congr rfl hG, Finset.sum_eq_single k]
    · rw [Nat.sub_self, Nat.stirlingSecond_zero, mul_one]
    · intro n hn hnk
      simp only [Finset.mem_range] at hn
      have hne : k - n ≠ 0 := by omega
      obtain ⟨K, hK⟩ := Nat.exists_eq_succ_of_ne_zero hne
      rw [hK, Nat.stirlingSecond_zero_succ, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hcon
  | succ v ih =>
    obtain rfl | hpos := Nat.eq_zero_or_pos k
    · have e : u + (v + 1) = (u + v) + 1 := by omega
      rw [e, Nat.stirlingSecond_succ_zero]
      rw [Finset.sum_eq_single 0]
      · have hu0 : Nat.stirlingSecond u 0 = 0 := by
        obtain ⟨u', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
        exact Nat.stirlingSecond_succ_zero u'
        rw [hu0, zero_mul]
      · intro n hn hnn
        simp only [Finset.mem_range] at hn
        have hn0 : n = 0 := by omega
        exact absurd hn0 hnn
      · intro hcon
        exact absurd (Finset.mem_range.mpr (by omega : (0 : ℕ) < 0 + 1)) hcon
    · obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have e : u + (v + 1) = (u + v) + 1 := by omega
      rw [e, Nat.stirlingSecond_succ_succ (u + v) K]
      have hstep : ∀ n ∈ Finset.range (K + 1),
        Nat.stirlingSecond u n *
          (∑ m ∈ Finset.range (v + 1 + 1),
            Nat.choose (v + 1) m * Nat.stirlingSecond m (K + 1 - n) * n ^ (v + 1 - m)) =
        (K + 1) * (Nat.stirlingSecond u n *
          (∑ m ∈ Finset.range (v + 1),
            Nat.choose v m * Nat.stirlingSecond m (K + 1 - n) * n ^ (v - m))) +
        (Nat.stirlingSecond u n *
          (∑ m ∈ Finset.range (v + 1),
            Nat.choose v m * Nat.stirlingSecond m (K - n) * n ^ (v - m))) := by
        intro n hn
        simp only [Finset.mem_range] at hn
        obtain ⟨K', hK'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K + 1 - n ≠ 0)
        have h1 : n + (K' + 1) = K + 1 := by omega
        have h2 : K - n = K' := by omega
        rw [hK', inner_succ n K' v, h1, h2]
        ring
      have hpeel : (∑ n ∈ Finset.range (K + 1 + 1), Nat.stirlingSecond u n *
        (∑ m ∈ Finset.range (v + 1 + 1),
          Nat.choose (v + 1) m * Nat.stirlingSecond m (K + 1 - n) * n ^ (v + 1 - m))) =
        (∑ n ∈ Finset.range (K + 1), Nat.stirlingSecond u n *
          (∑ m ∈ Finset.range (v + 1 + 1),
            Nat.choose (v + 1) m * Nat.stirlingSecond m (K + 1 - n) * n ^ (v + 1 - m))) +
        Nat.stirlingSecond u (K + 1) *
          (∑ m ∈ Finset.range (v + 1 + 1),
            Nat.choose (v + 1) m * Nat.stirlingSecond m (K + 1 - (K + 1)) *
              (K + 1) ^ (v + 1 - m)) :=
        Finset.sum_range_succ _ (K + 1)
      have e0 : K + 1 - (K + 1) = 0 := Nat.sub_self _
      have hF1 : (∑ n ∈ Finset.range (K + 1 + 1), Nat.stirlingSecond u n *
        (∑ m ∈ Finset.range (v + 1),
          Nat.choose v m * Nat.stirlingSecond m (K + 1 - n) * n ^ (v - m))) =
        (∑ n ∈ Finset.range (K + 1), Nat.stirlingSecond u n *
          (∑ m ∈ Finset.range (v + 1),
            Nat.choose v m * Nat.stirlingSecond m (K + 1 - n) * n ^ (v - m))) +
        Nat.stirlingSecond u (K + 1) *
          (∑ m ∈ Finset.range (v + 1),
            Nat.choose v m * Nat.stirlingSecond m 0 * (K + 1) ^ (v - m)) := by
        rw [Finset.sum_range_succ, e0]
      rw [hpeel, Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum,
        e0, inner_zero_succ (K + 1) v, ih (K + 1), ih K, hF1]
      ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[stirlingSecond_addition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondAddition.lean)
-/
@[path]
lemma stirlingSecond_addition
  {u v k : ℕ}
-- given
  (hu : 0 < u) :
-- imply
  Nat.stirlingSecond (u + v) k =
    ∑ n ∈ Finset.Icc 1 k, Nat.stirlingSecond u n *
    ∑ m ∈ Finset.Icc (k - n) v,
    Nat.choose v m * Nat.stirlingSecond m (k - n) * n ^ (v - m) := by
-- proof
  have h : ∀ n ∈ Finset.Icc 1 k,
    Nat.stirlingSecond u n *
    (∑ m ∈ Finset.Icc (k - n) v,
      Nat.choose v m * Nat.stirlingSecond m (k - n) * n ^ (v - m)) =
    Nat.stirlingSecond u n *
    (∑ m ∈ Finset.range (v + 1),
      Nat.choose v m * Nat.stirlingSecond m (k - n) * n ^ (v - m)) := by
    intro n _
    rw [inner_Icc_eq_range]
  have h1 : (∑ n ∈ Finset.Icc 1 k, Nat.stirlingSecond u n *
    ∑ m ∈ Finset.Icc (k - n) v,
      Nat.choose v m * Nat.stirlingSecond m (k - n) * n ^ (v - m)) =
    ∑ n ∈ Finset.Icc 1 k, Nat.stirlingSecond u n *
    ∑ m ∈ Finset.range (v + 1),
      Nat.choose v m * Nat.stirlingSecond m (k - n) * n ^ (v - m) :=
    Finset.sum_congr rfl h
  have houter : (∑ n ∈ Finset.Icc 1 k, Nat.stirlingSecond u n *
    ∑ m ∈ Finset.range (v + 1),
      Nat.choose v m * Nat.stirlingSecond m (k - n) * n ^ (v - m)) =
    ∑ n ∈ Finset.range (k + 1), Nat.stirlingSecond u n *
    ∑ m ∈ Finset.range (v + 1),
      Nat.choose v m * Nat.stirlingSecond m (k - n) * n ^ (v - m) :=
    outer_Icc_eq_range u k hu _
  rw [h1, houter]
  exact stirlingSecond_addition_range u v hu k

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
