import sympy.sets.stirling_partition
import sympy.Basic
open Stirling.conditionset


@[main]
private lemma main :
-- imply
  (parts 0 0).ncard = 1 := by
-- proof
  have : parts 0 0 = {∅} := by
    ext e
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    ·
      rintro ⟨x, -, rfl⟩
      simp
    ·
      rintro rfl
      exact ⟨Fin.elim0, ⟨by simp, by simp, fun i => i.elim0⟩, by simp⟩
  rw [this, Set.ncard_singleton]


-- created on 2026-10-07
