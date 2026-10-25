/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Instance.v1.Atlas.NumberTheoryI.code.GroupCounts
open scoped Classical


namespace GroupCounts

section Z4Z3

set_option maxHeartbeats 800000 in
lemma mulHomTriple_surjective (a b c : ZMod 4) (h : isSurjTriple a b c) :
    Function.Surjective (mulHomTriple a b c) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  intro t
  use Multiplicative.ofAdd (t.toAdd * x, t.toAdd * y, t.toAdd * z)
  show mulHomTriple a b c (Multiplicative.ofAdd (t.toAdd * x, t.toAdd * y, t.toAdd * z)) = t
  simp only [mulHomTriple, AddMonoidHom.toMultiplicative, addHomTriple,
        Multiplicative.ofAdd, Multiplicative.toAdd, Equiv.coe_fn_symm_mk,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.coe_fn_mk]
  have key : a * (t.toAdd * x) + b * (t.toAdd * y) + c * (t.toAdd * z) = t.toAdd := by
    have h1 : a * (t.toAdd * x) = t.toAdd * (a * x) := by ring
    have h2 : b * (t.toAdd * y) = t.toAdd * (b * y) := by ring
    have h3 : c * (t.toAdd * z) = t.toAdd * (c * z) := by ring
    rw [h1, h2, h3, ← mul_add, ← mul_add, hxyz, mul_one]
  exact key

lemma mulHomTriple_ker_index (a b c : ZMod 4) (h : isSurjTriple a b c) :
    (mulHomTriple a b c).ker.index = 4 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ (mulHomTriple_surjective a b c h)]
  rw [Subgroup.card_top, Nat.card_eq_fintype_card]; decide

lemma mulHomTriple_ker_isCyclic (a b c : ZMod 4)
    (h : isSurjTriple a b c) :
    IsCyclic (G₄₃ ⧸ (mulHomTriple a b c).ker) := by
  have e := QuotientGroup.quotientKerEquivOfSurjective
    (mulHomTriple a b c) (mulHomTriple_surjective a b c h)
  exact (MulEquiv.isCyclic e).mpr inferInstance

lemma addHom_eq_triple (f : (ZMod 4 × ZMod 4 × ZMod 4) →+ ZMod 4)
    (x y z : ZMod 4) :
    f (x, y, z) = f (1, 0, 0) * x + f (0, 1, 0) * y + f (0, 0, 1) * z := by
  have decomp : (x, y, z) = (x, (0 : ZMod 4), (0 : ZMod 4)) +
    ((0 : ZMod 4), y, (0 : ZMod 4)) + ((0 : ZMod 4), (0 : ZMod 4), z) := by
    ext <;> simp
  rw [decomp, map_add, map_add]
  have nsmul_cast : ∀ (n : ℕ) (a : ZMod 4), n • a = (n : ZMod 4) * a := by
    intros; simp
  have h1 : f (x, 0, 0) = f (1, 0, 0) * x := by
    have he : (x, (0 : ZMod 4), (0 : ZMod 4)) =
        x.val • ((1 : ZMod 4), (0 : ZMod 4), (0 : ZMod 4)) := by
      ext <;> simp [nsmul_cast, ZMod.natCast_val, ZMod.cast_id]
    rw [he, map_nsmul, nsmul_cast, ZMod.natCast_val, ZMod.cast_id, mul_comm]
  have h2 : f (0, y, 0) = f (0, 1, 0) * y := by
    have he : ((0 : ZMod 4), y, (0 : ZMod 4)) =
        y.val • ((0 : ZMod 4), (1 : ZMod 4), (0 : ZMod 4)) := by
      ext <;> simp [nsmul_cast, ZMod.natCast_val, ZMod.cast_id]
    rw [he, map_nsmul, nsmul_cast, ZMod.natCast_val, ZMod.cast_id, mul_comm]
  have h3 : f (0, 0, z) = f (0, 0, 1) * z := by
    have he : ((0 : ZMod 4), (0 : ZMod 4), z) =
        z.val • ((0 : ZMod 4), (0 : ZMod 4), (1 : ZMod 4)) := by
      ext <;> simp [nsmul_cast, ZMod.natCast_val, ZMod.cast_id]
    rw [he, map_nsmul, nsmul_cast, ZMod.natCast_val, ZMod.cast_id, mul_comm]
  rw [h1, h2, h3]

lemma mulHom_eq_triple (f : G₄₃ →* Multiplicative (ZMod 4)) :
    ∃ a b c : ZMod 4,
      ∀ g : G₄₃, f g = mulHomTriple a b c g := by
  let f' : (ZMod 4 × ZMod 4 × ZMod 4) →+ ZMod 4 := AddMonoidHom.toMultiplicative.symm f
  use f' (1, 0, 0), f' (0, 1, 0), f' (0, 0, 1)
  intro g
  have hf : f = AddMonoidHom.toMultiplicative f' := by simp [f']
  rw [hf]
  simp only [mulHomTriple]
  show AddMonoidHom.toMultiplicative f' g =
    AddMonoidHom.toMultiplicative (addHomTriple (f' (1, 0, 0)) (f' (0, 1, 0)) (f' (0, 0, 1))) g
  congr 1
  ext ⟨x, y, z⟩
  exact addHom_eq_triple f' x y z

end Z4Z3
end GroupCounts
