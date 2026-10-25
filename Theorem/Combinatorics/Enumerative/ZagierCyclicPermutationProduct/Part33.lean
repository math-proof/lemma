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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part30
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagVertical_diagonal {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    zagVertical (zagDiagonal e π) e = π := by
  simp only [zagVertical, zagDiagonal, mul_inv_rev, inv_inv]
  group

theorem zagDiagonal_of_vertical {n : ℕ}
    (D e π : Equiv.Perm (Fin n)) (hπ : π = zagVertical D e) :
    zagDiagonal e π = D := by
  subst π
  simp only [zagDiagonal, zagVertical, mul_inv_rev, inv_inv]
  group

theorem zagSlice_diagonal {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (x : Fin n)
    (hx : zagNontrivialAntiExceedance e π x) :
    zagDiagonal (zagSliceOrder e π x hx)
        (zagSliceVertical e π x hx) =
      zagDiagonal e π := by
  let D := zagDiagonal e π
  have hπ : π = zagVertical D e := (zagVertical_diagonal e π).symm
  exact zagDiagonal_of_vertical D _ _
    (zagSliceVertical_eq D e π x hx hπ)

end MetaMathlibExt
