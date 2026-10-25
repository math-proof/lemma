import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Combinatorics.Enumerative.GeneralizedCatalanSchroeder
open MathlibExtTest MathlibExtTest.Combinatorics MathlibExtTest.Combinatorics.Enumerative MathlibExtTest.Combinatorics.Enumerative.GeneralizedCatalanSchroeder
open scoped BigOperators


namespace MathlibExtTest.Combinatorics.Enumerative.GeneralizedCatalanSchroeder

/--
[catalan_recurrence_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/GeneralizedCatalanSchroeder.lean)
-/
@[path]
lemma catalan_recurrence_aux
  {m : ℕ} :
-- imply
  catalan (m + 2) = 2 * catalan (m + 1) + ∑ k ∈ Finset.range m, catalan (k + 1) * catalan (m - k) := by
-- proof
  rw [show m + 2 = (m + 1) + 1 by omega, catalan_succ',
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.sub_zero, catalan_zero, one_mul, Nat.sub_self, mul_one]
  omega

end MathlibExtTest.Combinatorics.Enumerative.GeneralizedCatalanSchroeder

namespace MathlibExtTest.Combinatorics.Enumerative.GeneralizedCatalanSchroeder

/--
[catalan_recurrence_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/GeneralizedCatalanSchroeder.lean)
-/
@[path]
lemma catalan_recurrence_rat
-- imply
  ∀ n : ℕ, 2 ≤ n → (catalan n : ℚ) = 2 * (catalan (n - 1) : ℚ) + ∑ k ∈ Finset.range (n - 2), (catalan (k + 1) : ℚ) * (catalan (n - k - 2) : ℚ) := by
-- proof
  intro n hn
  have hnat : catalan n = 2 * catalan (n - 1) +
    ∑ k ∈ Finset.range (n - 2), catalan (k + 1) * catalan (n - k - 2) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    have hn' : n = m + 2 := by omega
    rw [hn']
    have hsum :
      (∑ k ∈ Finset.range (m + 2 - 2),
        catalan (k + 1) * catalan (m + 2 - k - 2)) =
          ∑ k ∈ Finset.range m, catalan (k + 1) * catalan (m - k) := by
      apply Finset.sum_congr
      · congr 1
      · intro k hk
        congr 2
        simp only [Finset.mem_range] at hk
        omega
    rw [hsum]
    simpa only [show m + 2 - 1 = m + 1 by omega] using catalan_recurrence_aux m
  exact_mod_cast hnat

end MathlibExtTest.Combinatorics.Enumerative.GeneralizedCatalanSchroeder


-- created on 2026-10-23
