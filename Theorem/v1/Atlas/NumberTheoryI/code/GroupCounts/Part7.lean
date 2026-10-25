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
import Def.v1.Atlas.NumberTheoryI.code.GroupCounts.Part7
open scoped Classical


namespace GroupCounts

section Z4Z3

lemma carrier_of_cyclic_idx4_in_surjKernels
    (H : Subgroup G₄₃) (hidx : H.index = 4)
    (hcyc : IsCyclic (G₄₃ ⧸ H)) :
    subgroupToFinset₄₃ H ∈ surjKernelsMul := by
  haveI : Fintype (G₄₃ ⧸ H) := Fintype.ofFinite _
  have hcard_quot : Nat.card (G₄₃ ⧸ H) = 4 := by
    rw [← Subgroup.index_eq_card]; exact hidx
  have iso := zmodCyclicMulEquiv hcyc
  rw [hcard_quot] at iso
  let π := QuotientGroup.mk' H
  let f := iso.symm.toMonoidHom.comp π
  have hf_surj : Function.Surjective f := by
    apply Function.Surjective.comp iso.symm.surjective
    exact QuotientGroup.mk'_surjective H
  have hker : f.ker = H := by
    ext g
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, f]
    constructor
    · intro h
      have h1 : iso.symm (π g) = 1 := h
      have h2 : π g = iso 1 := by rw [← h1, MulEquiv.apply_symm_apply]
      rw [map_one] at h2
      exact (QuotientGroup.eq_one_iff g).mp h2
    · intro h
      have : π g = 1 := (QuotientGroup.eq_one_iff g).mpr h
      simp [this]
  obtain ⟨a, b, c, hf_eq⟩ := mulHom_eq_triple f
  have h_surj : isSurjTriple a b c := by
    obtain ⟨g, hg⟩ := hf_surj (Multiplicative.ofAdd (1 : ZMod 4))
    use g.toAdd.1, g.toAdd.2.1, g.toAdd.2.2
    have := hf_eq g
    rw [hg] at this
    simp only [mulHomTriple, AddMonoidHom.toMultiplicative, addHomTriple,
          Multiplicative.ofAdd, Multiplicative.toAdd, Equiv.coe_fn_symm_mk,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.coe_fn_mk] at this
    exact this.symm
  have hcarrier : subgroupToFinset₄₃ H = subgroupToFinset₄₃ (mulHomTriple a b c).ker := by
    ext g
    rw [subgroupToFinset₄₃_mem, subgroupToFinset₄₃_mem]
    rw [← hker]
    constructor
    · intro hg
      rw [MonoidHom.mem_ker]
      have : f g = mulHomTriple a b c g := hf_eq g
      rw [← this]
      rw [MonoidHom.mem_ker] at hg
      exact hg
    · intro hg
      rw [MonoidHom.mem_ker] at hg ⊢
      have : f g = mulHomTriple a b c g := hf_eq g
      rw [this]; exact hg
  rw [hcarrier]
  exact ker_carrier_mem_surjKernels a b c h_surj

end Z4Z3
end GroupCounts
