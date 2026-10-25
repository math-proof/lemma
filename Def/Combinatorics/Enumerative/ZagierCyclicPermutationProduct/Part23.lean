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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part22
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagResidualMergeOrder {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) : Equiv.Perm (Fin n) :=
  e * zagBlockSwap m.first m.middle (e.symm (π ε))
    m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)

noncomputable def zagResidualMergeVertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n) :
    Equiv.Perm (Fin n) :=
  π * zagTriangle (e m.first) (e m.middle) (π ε)

end MetaMathlibExt
