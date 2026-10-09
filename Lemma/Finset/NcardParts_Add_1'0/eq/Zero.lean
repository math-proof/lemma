import sympy.sets.stirling_partition
import sympy.Basic
open Stirling.conditionset


@[path]
private lemma main
-- given
  (n : ℕ) :
-- imply
  (parts (n + 1) 0).ncard = 0 := by
-- proof
  have : parts (n + 1) 0 = ∅ := by
    ext e
    simp only [Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro x hx _
    have : n ∈ Finset.univ.biUnion x := by rw [hx.1]; simp
    simp at this
  rw [this, Set.ncard_empty]


-- created on 2026-10-07
