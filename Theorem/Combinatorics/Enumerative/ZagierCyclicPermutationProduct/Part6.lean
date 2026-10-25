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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part6
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagTrivialAntiExceedance_not_exceedance {n : ℕ}
    (e π : Equiv.Perm (Fin n)) {x : Fin n}
    (hx : zagTrivialAntiExceedance e π x) : ¬zagExceedance e π x := by
  intro hexc
  have hmin := zagCycleMinPos_le e π (x := x) (y := x) Equiv.Perm.SameCycle.rfl
  simp only [zagExceedance] at hexc
  simp only [zagTrivialAntiExceedance] at hx
  rw [hx, e.symm_apply_apply] at hexc
  exact (not_lt_of_ge hmin) hexc

end MetaMathlibExt
