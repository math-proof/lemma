import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.GeneralizedBiPeriodicFibonacciZeroIndices
open MetaMathlibExt


/--
[generalized_biperiodic_fibonacci_zero_indices_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedBiPeriodicFibonacciZeroIndices.lean)
-/
@[path]
private lemma generalized_biperiodic_fibonacci_zero_indices_general_eq
  {a b c d m : ℕ}
  {F : ℕ → ℕ}
-- given
  (hm : 2 ≤ m)
  (hacoprime : Nat.Coprime a m)
  (hccoprime : Nat.Coprime c m)
  (hcd : c = d)
  (hF_zero : F 0 = 0)
  (hF_one : F 1 = 1)
  (hF_even : ∀ n : ℕ, F (2 * n + 2) = a * F (2 * n + 1) + c * F (2 * n))
  (hF_odd : ∀ n : ℕ, F (2 * n + 3) = b * F (2 * n + 2) + d * F (2 * n + 1)) :
-- imply
  ∃ l : ℕ,
    0 < l ∧
    (∀ n : ℕ, m ∣ F n ↔ l ∣ n) ∧
    (∀ r : ℕ, 0 < r → m ∣ F r → l ≤ r) := by
-- proof
  apply MetaMathlibExt.generalized_biperiodic_fibonacci_zero_indices_general hm hacoprime hccoprime hcd F hF_zero hF_one hF_even hF_odd

/--
[generalized_biperiodic_fibonacci_zero_indices](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GeneralizedBiPeriodicFibonacciZeroIndices.lean)
-/
@[path]
private lemma generalized_biperiodic_fibonacci_zero_indices_eq
  {a b c d m : ℕ}
  {F : ℕ → ℕ}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hd : 0 < d)
  (hm : 2 ≤ m)
  (hacoprime : Nat.Coprime a m)
  (hccoprime : Nat.Coprime c m)
  (hdcoprime : Nat.Coprime d m)
  (hcd : c = d)
  (hF_zero : F 0 = 0)
  (hF_one : F 1 = 1)
  (hF_even : ∀ n : ℕ, F (2 * n + 2) = a * F (2 * n + 1) + c * F (2 * n))
  (hF_odd : ∀ n : ℕ, F (2 * n + 3) = b * F (2 * n + 2) + d * F (2 * n + 1)) :
-- imply
  ∃ l : ℕ,
    0 < l ∧
    (∀ n : ℕ, m ∣ F n ↔ l ∣ n) ∧
    (∀ r : ℕ, 0 < r → m ∣ F r → l ≤ r) := by
-- proof
  apply MetaMathlibExt.generalized_biperiodic_fibonacci_zero_indices ha hb hc hd hm hacoprime hccoprime hdcoprime hcd F hF_zero hF_one hF_even hF_odd


-- created on 2026-10-20
