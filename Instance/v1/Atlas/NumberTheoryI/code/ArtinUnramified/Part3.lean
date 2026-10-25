/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Algebra.Set.Closure.eq.N.of.Eq
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Invariant.Basic
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Lemma247
import Def.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part12


noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

attribute [instance] CyclicExtensionData.instGroupG
  CyclicExtensionData.instFiniteG CyclicExtensionData.instCyclicG
  CyclicExtensionData.instCommGroupM CyclicExtensionData.instFiniteM
  CyclicExtensionData.instAction

instance tateH0Units.finite [Fintype (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)] :
    Finite (tateH0Units K L) := by
  classical


  set n := Fintype.card (L ≃ₐ[K] L) with hn_def
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos

  haveI : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  haveI : Group.FG (unitsFixed K L) := by
    rw [Group.fg_iff_monoid_fg] at *
    have hfgA : AddGroup.FG (Additive (𝓞 L)ˣ) := by
      rw [AddGroup.fg_iff_addMonoid_fg]; exact Monoid.fg_iff_add_fg.mp ‹_›
    have hfgAH : AddGroup.FG (Additive ↥(unitsFixed K L)) := by
      rw [← Module.Finite.iff_addGroup_fg] at *
      exact Module.Finite.of_injective
        ((unitsFixed K L).toAddSubgroup.toIntSubmodule.subtype) Subtype.val_injective
    rw [Monoid.fg_iff_add_fg]; exact AddGroup.fg_iff_addMonoid_fg.mp hfgAH

  have hfin : (powMonoidHom (α := ↥(unitsFixed K L)) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg (unitsFixed K L) hn_ne


  have hle : (powMonoidHom (α := ↥(unitsFixed K L)) n).range ≤
      (normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L) := by
    intro u hmem
    rw [MonoidHom.mem_range] at hmem
    obtain ⟨v, heq⟩ := hmem
    simp only [Subgroup.mem_subgroupOf]


    have hfixed : ∀ σ : (L ≃ₐ[K] L), σ • (v : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) := fun σ =>
      v.property σ

    have hnorm : normMapUnits K L (v : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) ^ n := by
      show ∏ σ : (L ≃ₐ[K] L), σ • (v : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) ^ n
      simp_rw [hfixed]
      rw [Finset.prod_const, Finset.card_univ, hn_def]

    have hval : (u : (𝓞 L)ˣ) = (v : (𝓞 L)ˣ) ^ n := by
      have := congr_arg Subtype.val heq
      simp [powMonoidHom_apply] at this
      exact this.symm
    rw [show (u : (𝓞 L)ˣ) = normMapUnits K L (v : (𝓞 L)ˣ) from by rw [hnorm, ← hval]]
    exact MonoidHom.mem_range.mpr ⟨(v : (𝓞 L)ˣ), rfl⟩

  haveI : ((normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L)).FiniteIndex :=
    Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

instance tateMinus1Units.finite [Fintype (L ≃ₐ[K] L)] [IsCyclic (L ≃ₐ[K] L)] :
    Finite (tateMinus1Units K L) := by
  classical

  set n := Fintype.card (L ≃ₐ[K] L) with hn_def
  have hn_ne : n ≠ 0 := Fintype.card_ne_zero

  haveI : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  haveI : Group.FG ↥(normKerUnits K L) :=
    (Group.fg_iff_subgroup_fg _).mpr (subgroup_fg_of_comm_fg (L := L) _)

  haveI hpow : (powMonoidHom (α := ↥(normKerUnits K L)) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg _ hn_ne


  have hle : (powMonoidHom (α := ↥(normKerUnits K L)) n).range ≤
      (augmentationUnitsSubgroup K L).subgroupOf (normKerUnits K L) := by
    intro ⟨v, hv_mem⟩ hv_range
    rw [MonoidHom.mem_range] at hv_range
    obtain ⟨⟨w, hw_mem⟩, hw_eq⟩ := hv_range
    simp only [Subgroup.mem_subgroupOf]
    have hv_eq : v = w ^ n := by
      have := congr_arg Subtype.val hw_eq
      simpa [SubgroupClass.coe_pow, powMonoidHom_apply] using this.symm
    rw [hv_eq]
    have hw_ker : normMapUnits K L w = 1 := by
      have := hw_mem
      rwa [normKerUnits, MonoidHom.mem_ker] at this
    exact pow_card_mem_augmentationUnitsSubgroup K L w hw_ker

  haveI : ((augmentationUnitsSubgroup K L).subgroupOf (normKerUnits K L)).FiniteIndex :=
    Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

end ArtinUnramified
end
