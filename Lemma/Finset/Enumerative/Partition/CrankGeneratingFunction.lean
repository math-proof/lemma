import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.CrankGeneratingFunction
open MetaMathlibExt


/--
[crank_nonneg_partition_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crank_nonneg_partition_count_eq
  {N : ℕ} :
-- imply
  Fintype.card { P : Nat.Partition N //
    0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
    else (((P.parts.filter
    (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
    - (Multiset.count 1 P.parts : ℤ)))}
    = ∑ n ∈ Finset.range (N + 1),
    (if (n + 1) * n / 2 ≤ N
    then (-1 : ℤ) ^ n * (Fintype.card (Nat.Partition (N - (n + 1) * n / 2)) : ℤ)
    else 0) := by
-- proof
  apply MetaMathlibExt.crank_nonneg_partition_count N


-- created on 2026-10-20
