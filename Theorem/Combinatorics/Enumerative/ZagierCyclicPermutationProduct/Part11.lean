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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part11
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagTriangle_apply_left {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) :
    zagTriangle a b c a = b := by
  simp only [zagTriangle, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  rw [Equiv.swap_apply_of_ne_of_ne hab.symm hbc]

@[simp]
theorem zagTriangle_apply_middle {α : Type*} [DecidableEq α]
    (a b c : α) : zagTriangle a b c b = c := by
  simp [zagTriangle, Equiv.Perm.mul_apply]

theorem zagTriangle_apply_of_ne {α : Type*} [DecidableEq α]
    {a b c x : α} (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    zagTriangle a b c x = x := by
  simp only [zagTriangle, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb,
    Equiv.swap_apply_of_ne_of_ne hxa hxc]

theorem zagTriangle_mul_reverse {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    zagTriangle a b c * zagTriangle a c b = 1 := by
  ext x
  simp only [zagTriangle, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem zagTriangle_inv {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (zagTriangle a b c)⁻¹ = zagTriangle a c b := by
  have hrev := zagTriangle_mul_reverse hab hac hbc
  calc
    (zagTriangle a b c)⁻¹ = (zagTriangle a b c)⁻¹ * 1 := by rw [mul_one]
    _ = (zagTriangle a b c)⁻¹ *
        (zagTriangle a b c * zagTriangle a c b) := by rw [hrev]
    _ = zagTriangle a c b := by group

end MetaMathlibExt
