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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagCycleMinPos_mem {n : ℕ} (e π : Equiv.Perm (Fin n))
    (x : Fin n) : π.SameCycle (e (zagCycleMinPos e π x)) x := by
  classical
  rw [zagCycleMinPos]
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter fun i => π.SameCycle (e i) x) _)).2

theorem zagCycleMinPos_le {n : ℕ} (e π : Equiv.Perm (Fin n))
    {x y : Fin n} (hxy : π.SameCycle y x) :
    zagCycleMinPos e π x ≤ e.symm y := by
  classical
  exact Finset.min'_le _ _ (by simp [hxy])

theorem zagCycleMinPos_eq_of_sameCycle {n : ℕ}
    (e π : Equiv.Perm (Fin n)) {x y : Fin n} (hxy : π.SameCycle x y) :
    zagCycleMinPos e π x = zagCycleMinPos e π y := by
  apply le_antisymm
  · simpa using zagCycleMinPos_le e π
      ((zagCycleMinPos_mem e π y).trans hxy.symm)
  · simpa using zagCycleMinPos_le e π
      ((zagCycleMinPos_mem e π x).trans hxy)

end MetaMathlibExt
