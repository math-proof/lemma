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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part3
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zag_cycleMinPos_mem_cycleMinima {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (x : Fin n) :
    zagCycleMinPos e π x ∈ zagCycleMinima e π := by
  rw [zag_mem_cycleMinima_iff]
  exact zagCycleMinPos_eq_of_sameCycle e π (zagCycleMinPos_mem e π x)

theorem zagCycleMinima_not_same_of_lt {n : ℕ}
    (e π : Equiv.Perm (Fin n)) {i j : Fin n}
    (hi : i ∈ zagCycleMinima e π) (hj : j ∈ zagCycleMinima e π)
    (hij : i < j) : ¬π.SameCycle (e i) (e j) := by
  intro hsame
  have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
  rw [(zag_mem_cycleMinima_iff e π i).mp hi,
    (zag_mem_cycleMinima_iff e π j).mp hj] at hmin
  exact hij.ne hmin

end MetaMathlibExt
