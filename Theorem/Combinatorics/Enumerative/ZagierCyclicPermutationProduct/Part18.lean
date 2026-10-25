/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part18
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagCutCandidates_nonempty {n : ℕ}
    (e π : Equiv.Perm (Fin n)) {ε : Fin n}
    (hε : zagNontrivialAntiExceedance e π ε) :
    (zagCutCandidates e π ε).Nonempty := by
  classical
  refine ⟨e.symm ε, ?_⟩
  rw [zagCutCandidates, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, zagNTAE_image_lt e π hε,
    zagCutHit e π ε - 1, ?_⟩
  refine ⟨by have := zagCutHit_two_le e π hε; omega,
    by have := zagCutHit_two_le e π hε; omega, ?_⟩
  simpa using zagCutHit_pred e π hε

end MetaMathlibExt
