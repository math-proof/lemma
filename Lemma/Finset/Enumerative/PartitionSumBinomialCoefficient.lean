import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.PartitionSumBinomialCoefficient
open Finset
open MetaMathlibExt


/--
[choose_mul_eq_partition_sum_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PartitionSumBinomialCoefficient.lean)
-/
@[path]
private lemma choose_mul_eq_partition_sum_unconditional_eq
  {n m l : ℕ} :
-- imply
  Nat.choose (n * m) l =
    ∑ s : {s : Fin m → Fin (l + 1) //
    ∑ k : Fin m, ((k : ℕ) + 1) * (s k : ℕ) = l},
    ∏ k : Fin m,
    Nat.choose
    (n - ∑ i : Fin m, if k < i then (s.1 i : ℕ) else 0)
    (s.1 k : ℕ) *
    Nat.choose m ((k : ℕ) + 1) ^ (s.1 k : ℕ) := by
-- proof
  apply MetaMathlibExt.choose_mul_eq_partition_sum_unconditional n m l

/--
[choose_mul_eq_partition_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PartitionSumBinomialCoefficient.lean)
-/
@[path]
private lemma choose_mul_eq_partition_sum_eq
  {n m l : ℕ}
-- given
  (hn : 0 < n)
  (hm : 0 < m)
  (hl : 0 < l)
  (hl_lower : 1 ≤ l)
  (hl_upper : l ≤ n * m) :
-- imply
  Nat.choose (n * m) l =
    ∑ s : {s : Fin m → Fin (l + 1) //
    ∑ k : Fin m, ((k : ℕ) + 1) * (s k : ℕ) = l},
    ∏ k : Fin m,
    Nat.choose
    (n - ∑ i : Fin m, if k < i then (s.1 i : ℕ) else 0)
    (s.1 k : ℕ) *
    Nat.choose m ((k : ℕ) + 1) ^ (s.1 k : ℕ) := by
-- proof
  apply MetaMathlibExt.choose_mul_eq_partition_sum n m l hn hm hl hl_lower hl_upper


-- created on 2026-10-20
