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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part19
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagSliceOrder {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    Equiv.Perm (Fin n) :=
  e * zagBlockSwap (zagCycleMinPos e π ε) (e.symm (π ε))
    (zagCutPos e π ε hε)
    (zagNTAE_min_lt_image e π hε)
    (zagImage_lt_cutPos e π ε hε)

noncomputable def zagSliceVertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    Equiv.Perm (Fin n) :=
  π * zagTriangle (e (zagCycleMinPos e π ε)) (π ε)
    (e (zagCutPos e π ε hε))

end MetaMathlibExt
