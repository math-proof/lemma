import Mathlib
import sympy.Basic
open scoped BigOperators


namespace MetaMathlibExt

/--
[vander_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/StrehlFranel.lean)
-/
@[path]
private lemma vander_single (a b t : ℕ) :
  Nat.choose (a + b) t =
    ∑ i ∈ Finset.range (t + 1), Nat.choose a i * Nat.choose b (t - i) := by
  rwa [Nat.add_choose_eq a b t]
    (fun i j => Nat.choose a i * Nat.choose b j) t

end MetaMathlibExt

namespace MetaMathlibExt

/--
[inner_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/StrehlFranel.lean)
-/
@[path]
private lemma inner_sum (n j : ℕ) (hj : j ≤ n) :
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k) ^ 2 * (Nat.choose k j * Nat.choose k (n - j)) =
    (Nat.choose n j) ^ 3 := by
  have hjm : j ≤ max j (n - j) := Nat.le_max_left _ _
  have hnm : n - j ≤ max j (n - j) := Nat.le_max_right _ _
  have hsub : Finset.Ico (max j (n - j)) (n + 1) ⊆ Finset.range (n + 1) := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    rwa [Finset.mem_range]
  have hdrop : ∀ x ∈ Finset.range (n + 1), x ∉ Finset.Ico (max j (n - j)) (n + 1) →
    (Nat.choose n x) ^ 2 * (Nat.choose x j * Nat.choose x (n - j)) = 0 := by
    intro x hx hxI
    rw [Finset.mem_range] at hx
    rw [Finset.mem_Ico] at hxI
    have hxm : x < max j (n - j) := lt_of_not_ge (fun hle => hxI ⟨hle, hx⟩)
    have hdis : x < j ∨ x < n - j := by omega
    obtain h1 | h2 := hdis
    · rw [Nat.choose_eq_zero_of_lt h1, zero_mul, mul_zero]
    · rw [Nat.choose_eq_zero_of_lt h2, mul_zero, mul_zero]
  have hterm : ∀ k ∈ Finset.Ico (max j (n - j)) (n + 1),
    (Nat.choose n k) ^ 2 * (Nat.choose k j * Nat.choose k (n - j)) =
      Nat.choose n j * Nat.choose n (n - j) *
        (Nat.choose (n - j) (k - j) * Nat.choose j (k - (n - j))) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h1 : j ≤ k := le_trans hjm hk.1
    have h2 : n - j ≤ k := le_trans hnm hk.1
    have e1 := Nat.choose_mul (n := n) (k := k) (s := j) h1
    have e2 := Nat.choose_mul (n := n) (k := k) (s := n - j) h2
    have hnn : n - (n - j) = j := by omega
    rw [hnn] at e2
    have rearr : (Nat.choose n k * Nat.choose n k) *
      (Nat.choose k j * Nat.choose k (n - j)) =
      (Nat.choose n k * Nat.choose k j) *
        (Nat.choose n k * Nat.choose k (n - j)) := by ring
    rw [pow_two, rearr, e1, e2]
    ring
  have hV : ∑ k ∈ Finset.Ico (max j (n - j)) (n + 1),
    (Nat.choose (n - j) (k - j) * Nat.choose j (k - (n - j))) =
    Nat.choose n (n - j) := by
    by_cases h : j ≤ n - j
    · have hmA : max j (n - j) = n - j := Nat.max_eq_right h
      rw [hmA]
      have hshape : n + 1 = (n - j) + (j + 1) := by omega
      have hcancel : n - j + (j + 1) - (n - j) = j + 1 := by omega
      rw [hshape, Finset.sum_Ico_eq_sum_range, hcancel]
      have hpoint : ∀ i ∈ Finset.range (j + 1),
        Nat.choose (n - j) ((n - j + i) - j) * Nat.choose j ((n - j + i) - (n - j)) =
          Nat.choose j i * Nat.choose (n - j) (j - i) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have hsub1 : (n - j + i) - j = (n - j) - (j - i) := by omega
        have hsub2 : (n - j + i) - (n - j) = i := by omega
        have hle : j - i ≤ n - j := by omega
        rw [hsub1, Nat.choose_symm hle, hsub2]
        exact mul_comm _ _
      rw [Finset.sum_congr rfl hpoint]
      have hVs := vander_single j (n - j) j
      have hjn : j + (n - j) = n := by omega
      rw [hjn] at hVs
      have hss : Nat.choose n (n - j) = Nat.choose n j := Nat.choose_symm hj
      rwa [hss]
    · have hlt : n - j < j := lt_of_not_ge h
      have hle : n - j ≤ j := le_of_lt hlt
      have hmB : max j (n - j) = j := Nat.max_eq_left hle
      rw [hmB]
      have hshape : n + 1 = j + ((n - j) + 1) := by omega
      have hcancel : j + (n - j + 1) - j = (n - j) + 1 := by omega
      rw [hshape, Finset.sum_Ico_eq_sum_range, hcancel]
      have hpoint : ∀ i ∈ Finset.range ((n - j) + 1),
        Nat.choose (n - j) ((j + i) - j) * Nat.choose j ((j + i) - (n - j)) =
          Nat.choose (n - j) i * Nat.choose j ((n - j) - i) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have hsub1 : (j + i) - j = i := by omega
        have hsub2 : (j + i) - (n - j) = j - ((n - j) - i) := by omega
        have hle2 : (n - j) - i ≤ j := by omega
        rw [hsub1, hsub2, Nat.choose_symm hle2]
      rw [Finset.sum_congr rfl hpoint]
      have hVs := vander_single (n - j) j (n - j)
      have hjn : (n - j) + j = n := by omega
      rwa [hjn] at hVs
  rw [← Finset.sum_subset hsub hdrop, Finset.sum_congr rfl hterm, ← Finset.mul_sum, hV]
  have hss : Nat.choose n (n - j) = Nat.choose n j := Nat.choose_symm hj
  rw [hss]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[strehl_franel_binomial_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/StrehlFranel.lean)
-/
@[path]
lemma strehl_franel_binomial_identity
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 * Nat.choose (2 * k) n) =
    ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 3 := by
-- proof
  have hexpand : ∀ k ∈ Finset.range (n + 1),
    (Nat.choose n k) ^ 2 * Nat.choose (2 * k) n =
      ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n k) ^ 2 * (Nat.choose k j * Nat.choose k (n - j)) := by
    intro k _
    rw [two_mul k, vander_single k k n, Finset.mul_sum]
  have hLHS : (∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 * Nat.choose (2 * k) n) =
    ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      (Nat.choose n k) ^ 2 * (Nat.choose k j * Nat.choose k (n - j)) :=
    Finset.sum_congr rfl hexpand
  rw [hLHS, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  exact inner_sum n j (by omega)
end MetaMathlibExt



-- created on 2026-10-20
-- updated on 2026-10-23
