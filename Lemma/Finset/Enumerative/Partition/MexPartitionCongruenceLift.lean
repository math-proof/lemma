import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift
open MetaMathlibExt


/--
[mesh_partition_congruence_lift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mesh_partition_congruence_lift_eq
  {m a b : ℕ}
-- given
  (hm : 0 < m)
  (ha : 0 < a)
  (hb : b < a)
  (hbase : ∀ n : ℕ, m ∣ Fintype.card (Nat.Partition (a * n + b))) :
-- imply
  ∀ t : ℕ, 0 < t →
    (∀ n : ℕ, m ∣ (@Finset.filter (Nat.Partition (a * n + b))
    (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (a * t) = (a * t) % (a * t) ∧
    μ ∉ lam.parts ∧
    (∀ k : ℕ, 0 < k → k < μ → k % (a * t) = (a * t) % (a * t) →
    k ∈ lam.parts) ∧
    μ % (2 * (a * t)) = (a * t) % (2 * (a * t)))
    (Classical.decPred _) Finset.univ).card) ∧
    (∀ n : ℕ, m ∣ (@Finset.filter (Nat.Partition (a * n + b))
    (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (2 * a * t) = (a * t) % (2 * a * t) ∧
    μ ∉ lam.parts ∧
    (∀ k : ℕ, 0 < k → k < μ → k % (2 * a * t) = (a * t) % (2 * a * t) →
    k ∈ lam.parts) ∧
    μ % (2 * (2 * a * t)) = (a * t) % (2 * (2 * a * t)))
    (Classical.decPred _) Finset.univ).card) := by
-- proof
  apply MetaMathlibExt.mesh_partition_congruence_lift m a b hm ha hb hbase


-- created on 2026-10-20
