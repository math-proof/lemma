import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MeshPatternGeneratingFunction
open MetaMathlibExt


/--
[meshPatternGeneratingFunction_eq_factorial_mul_prod_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternGeneratingFunction.lean)
-/
@[path]
private lemma meshPatternGeneratingFunction_eq_factorial_mul_prod_general_eq
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
  apply MetaMathlibExt.meshPatternGeneratingFunction_eq_factorial_mul_prod_general P n k x hk hnk hbase hstep

/--
[meshPatternGeneratingFunction_eq_factorial_mul_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternGeneratingFunction.lean)
-/
@[path]
private lemma meshPatternGeneratingFunction_eq_factorial_mul_prod_eq
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
  apply MetaMathlibExt.meshPatternGeneratingFunction_eq_factorial_mul_prod P n k x hk hnk hbase hstep


-- created on 2026-10-20
