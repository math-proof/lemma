import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Matroid.MatroidPartition
open MathlibExt.Combinatorics.Matroid.MatroidPartitionWanted


/--
[edmonds_matroid_partition'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/MatroidPartition.lean)
-/
@[path]
private lemma edmonds_matroid_partition'_eq
  [Finite E]
  {M : Matroid E}
  {S : Set E}
  {k : ℕ} :
-- imply
  (∃ J : Fin k → Set E, (∀ i, M.Indep (J i)) ∧ S = ⋃ i, J i) ↔
    ∀ X : Set E, X ⊆ S → (X.ncard : ℕ∞) ≤ (k : ℕ∞) * M.eRk X := by
-- proof
  apply MathlibExt.Combinatorics.Matroid.MatroidPartitionWanted.edmonds_matroid_partition'

/--
[edmonds_matroid_partition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/MatroidPartition.lean)
-/
@[path]
private lemma edmonds_matroid_partition_eq
  [Fintype E] [DecidableEq E]
  {M : Matroid E}
  {S : Set E}
  {k : ℕ}
-- given
  (hM : M.E = Set.univ) :
-- imply
  (∃ J : Fin k → Set E, (∀ i, M.Indep (J i)) ∧ S = ⋃ i, J i) ↔
    ∀ X : Set E, X ⊆ S → (X.ncard : ℕ∞) ≤ (k : ℕ∞) * M.eRk X := by
-- proof
  apply MathlibExt.Combinatorics.Matroid.MatroidPartitionWanted.edmonds_matroid_partition hM


-- created on 2026-10-20
