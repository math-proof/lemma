import sympy.sets.stirling_partition
import sympy.Basic
open Stirling.conditionset


@[path]
private lemma main
  {n k : ℕ}
  {x : Fin k → Finset ℕ}
-- given
  (hx : x ∈ Stirling.conditionset n k)
  (i : Fin k) :
-- imply
  x i ⊆ Finset.range n := by
-- proof
  rw [← hx.1]
  exact Finset.subset_biUnion_of_mem x (Finset.mem_univ i)


-- created on 2026-10-07
