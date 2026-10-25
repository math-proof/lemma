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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part2
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagQuotientMinPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    Quotient (Equiv.Perm.SameCycle.setoid π) → Fin n :=
  Quotient.lift (zagCycleMinPos e π)
    (fun _x _y h => zagCycleMinPos_eq_of_sameCycle e π h)

noncomputable def zagCycleMinima {n : ℕ}
    (e π : Equiv.Perm (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => zagCycleMinPos e π (e i) = i

end MetaMathlibExt
