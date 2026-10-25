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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part13
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagConj_swap {α : Type*} [DecidableEq α]
    (e : Equiv.Perm α) (a b : α) :
    e * Equiv.swap a b * e⁻¹ = Equiv.swap (e a) (e b) := by
  ext x
  simpa using e.injective.map_swap a b (e.symm x)

theorem zagConj_triangle {α : Type*} [DecidableEq α]
    (e : Equiv.Perm α) (a b c : α) :
    e * zagTriangle a b c * e⁻¹ = zagTriangle (e a) (e b) (e c) := by
  simp only [zagTriangle]
  rw [show e * (Equiv.swap a c * Equiv.swap a b) * e⁻¹ =
      (e * Equiv.swap a c * e⁻¹) * (e * Equiv.swap a b * e⁻¹) by group,
    zagConj_swap, zagConj_swap]

theorem zagHorizontal_blockSwap {n : ℕ} (e : Equiv.Perm (Fin n))
    (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    zagHorizontal (e * zagBlockSwap a b c hab hbc) =
      zagHorizontal e * zagTriangle (e a) (e b) (e c) := by
  simp only [zagHorizontal, mul_inv_rev]
  rw [show (e * zagBlockSwap a b c hab hbc) * finRotate n *
        ((zagBlockSwap a b c hab hbc)⁻¹ * e⁻¹) =
      e * (zagBlockSwap a b c hab hbc * finRotate n *
        (zagBlockSwap a b c hab hbc)⁻¹) * e⁻¹ by group,
    zagBlockSwap_conj_finRotate]
  rw [show e * (finRotate n * zagTriangle a b c) * e⁻¹ =
      (e * finRotate n * e⁻¹) * (e * zagTriangle a b c * e⁻¹) by group,
    zagConj_triangle]

end MetaMathlibExt
