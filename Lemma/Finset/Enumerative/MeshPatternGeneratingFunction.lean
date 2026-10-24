import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[meshPatternGeneratingFunction_eq_factorial_mul_prod_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternGeneratingFunction.lean)
-/
@[path]
lemma meshPatternGeneratingFunction_eq_factorial_mul_prod_general
  [CommSemiring R]
  {P : ℕ → ℕ → R}
  {n k : ℕ}
  {x : R}
-- given
  (hk : 0 < k)
  (hnk : k ≤ n)
  (hbase : P (k - 1) k = (Nat.factorial (k - 1) : R))
  (hstep : ∀ m : ℕ, k ≤ m → P m k = (x + ((m - 1 : ℕ) : R)) * P (m - 1) k) :
-- imply
  P n k =
      (Nat.factorial (k - 1) : R) *
        ∏ i ∈ Finset.range (n - k + 1),
          (x + ((k - 1 + i : ℕ) : R)) := by
-- proof
  induction n, hnk using Nat.le_induction with
  | base =>
    have h1 := hstep k (by omega : k ≤ k)
    rw [hbase] at h1
    rw [h1]
    have hkk : k - k + 1 = 1 := by omega
    rw [hkk, Finset.prod_range_succ]
    simp
    ring
  | succ n hkn ih =>
    have hstep' := hstep (n + 1) (by omega : k ≤ n + 1)
    have hn1 : n + 1 - 1 = n := by omega
    rw [hn1] at hstep'
    rw [hstep', ih]
    have hrange : n + 1 - k + 1 = (n - k + 1) + 1 := by omega
    have hcast : (k - 1 + (n - k + 1) : ℕ) = n := by omega
    have hprod : (∏ i ∈ Finset.range (n + 1 - k + 1),
      (x + ((k - 1 + i : ℕ) : R))) =
      (∏ i ∈ Finset.range (n - k + 1),
        (x + ((k - 1 + i : ℕ) : R))) *
      (x + (((k - 1 + (n - k + 1) : ℕ)) : R)) := by
      rw [hrange, Finset.prod_range_succ]
    rw [hprod, hcast]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[meshPatternGeneratingFunction_eq_factorial_mul_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternGeneratingFunction.lean)
-/
@[path]
lemma meshPatternGeneratingFunction_eq_factorial_mul_prod
  {P : ℕ → ℕ → ℝ → ℝ}
  {n k : ℕ}
  {x : ℝ}
-- given
  (hk : 0 < k)
  (hnk : k ≤ n)
  (hbase : P (k - 1) k x = (Nat.factorial (k - 1) : ℝ))
  (hstep : ∀ m : ℕ, k ≤ m → P m k x = (x + ((m - 1 : ℕ) : ℝ)) * P (m - 1) k x) :
-- imply
  P n k x =
      (Nat.factorial (k - 1) : ℝ) *
        ∏ i ∈ Finset.range (n - k + 1),
          (x + ((k - 1 + i : ℕ) : ℝ)) := by
-- proof
  exact meshPatternGeneratingFunction_eq_factorial_mul_prod_general (fun m r => P m r x) n k x
    hk hnk hbase hstep

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
