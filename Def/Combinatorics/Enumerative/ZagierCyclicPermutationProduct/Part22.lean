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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part21
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagMergeOrder {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    Equiv.Perm (Fin n) :=
  e * zagBlockSwap m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third

noncomputable def zagMergeVertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    Equiv.Perm (Fin n) :=
  π * zagTriangle (e m.first) (e m.middle) (e m.third)

noncomputable def zagMergePoint {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) : Fin n :=
  (zagMergeVertical e π m).symm (e m.third)

end MetaMathlibExt
