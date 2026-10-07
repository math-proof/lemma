import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.Subset_Range.of.In_Conditionset
open Finset Stirling.conditionset


@[main]
private lemma main
-- given
  (k : ℕ) :
-- imply
  (parts 0 (k + 1)).ncard = 0 := by
-- proof
  have : parts 0 (k + 1) = ∅ := by
    ext e
    simp only [Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro x hx _
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (hx.2.2 0)
    have := Subset_Range.of.In_Conditionset hx 0 ha
    simp at this
  rw [this, Set.ncard_empty]


-- created on 2026-10-07
