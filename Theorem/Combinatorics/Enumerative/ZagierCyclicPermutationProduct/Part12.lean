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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part12
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagTriangle_val {n : ℕ} {a b c x : Fin n}
    (hab : a < b) (hbc : b < c) :
    (zagTriangle a b c x : ℕ) = zagTriangleNat a b c x := by
  simp only [zagTriangle, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    zagTriangleNat]
  split_ifs <;> simp_all <;> omega

theorem zagBlockSwapNat_rotate_unswap {a b c p last : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < last + 1) (hp : p < last + 1) :
    zagBlockSwapNat a b c
        (zagRotateNat last (zagBlockUnswapNat a b c p)) =
      zagRotateNat last (zagTriangleNat a b c p) := by
  simp only [zagBlockSwapNat, zagBlockUnswapNat, zagRotateNat,
    zagTriangleNat]
  split_ifs <;> omega

theorem zagBlockSwap_conj_finRotate {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockSwap a b c hab hbc * finRotate n *
        (zagBlockSwap a b c hab hbc)⁻¹ =
      finRotate n * zagTriangle a b c := by
  have hn : n ≠ 0 := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  ext x
  simp only [Equiv.Perm.mul_apply, zagBlockSwap_val, coe_finRotate,
    Fin.ext_iff, zagBlockSwap_inv_val, Fin.val_last, zagTriangle_val hab hbc]
  simpa only [zagRotateNat] using
    zagBlockSwapNat_rotate_unswap (p := x) (last := m) hab hbc c.isLt x.isLt

end MetaMathlibExt
