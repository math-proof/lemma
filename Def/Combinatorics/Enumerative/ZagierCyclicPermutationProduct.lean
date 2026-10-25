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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagCycleMinPos {n : ℕ} (e π : Equiv.Perm (Fin n))
    (x : Fin n) : Fin n :=
  let orbitPositions := Finset.univ.filter fun i => π.SameCycle (e i) x
  orbitPositions.min' ⟨e.symm x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    simpa using (Equiv.Perm.SameCycle.rfl : π.SameCycle x x)⟩⟩

end MetaMathlibExt
