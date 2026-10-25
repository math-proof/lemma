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
import Structure.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part3


noncomputable section

open scoped Pointwise

open NumberField

attribute [instance] IdealGroupData.instGroupG IdealGroupData.instFiniteG
  IdealGroupData.instCyclicG IdealGroupData.instCommGroupIL
  IdealGroupData.instCommGroupIK IdealGroupData.instAction

def IdealGroupData.fixedIdeals (d : IdealGroupData) : Subgroup d.I_L :=
  FixedPoints.subgroup d.G d.I_L

def IdealGroupData.extendedIdeals (d : IdealGroupData) : Subgroup d.I_L :=
  d.extensionMap.range

def IdealGroupData.normImage (d : IdealGroupData) : Subgroup d.I_K :=
  d.normMap.range

noncomputable def IdealGroupData.cohomNormImage (d : IdealGroupData) : Subgroup d.I_L where
  carrier := Set.range (fun I : d.I_L =>
    haveI := Fintype.ofFinite d.G
    ∏ g : d.G, g • I)
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    simp only [smul_mul', Finset.prod_mul_distrib]
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a⁻¹, ?_⟩
    simp only [smul_inv']
    rw [Finset.prod_inv_distrib]

noncomputable def quotient_equiv_image_quotient
    {A C : Type*} [CommGroup A] [CommGroup C]
    (f : A →* C) (B : Subgroup A) (hB : f.ker ≤ B) :
    A ⧸ B ≃* ↥f.range ⧸ (B.map f).subgroupOf f.range := by
  let g : A →* ↥f.range ⧸ (B.map f).subgroupOf f.range :=
    (QuotientGroup.mk' _).comp (f.rangeRestrict)
  have hg_surj : Function.Surjective g := by
    intro q
    obtain ⟨⟨c, hc⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨a, rfl⟩ := hc
    exact ⟨a, rfl⟩
  have hg_ker : g.ker = B := by
    ext a
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, g]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, hfb⟩
      have hab : a * b⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have : f b = f a := by
          change f b = (f.rangeRestrict a : C)
          simp only [MonoidHom.coe_rangeRestrict]
          exact hfb
        rw [this, mul_inv_cancel]
      exact Subgroup.mul_mem_cancel_right B (Subgroup.inv_mem B hb) |>.mp (hB hab)
    · intro ha
      exact ⟨a, ha, rfl⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hg_ker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg_surj))

def TateCohomologyAllTrivial (G : Type*) [Group G] [Finite G]
    (M : Type*) [CommGroup M] [MulDistribMulAction G M] : Prop := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  exact (
    (∀ m : M, (∀ g : G, g • m = m) → ∃ a : M, m = ∏ g : G, g • a) ∧
    (∀ m : M, (∏ g : G, g • m) = 1 →
      m ∈ Subgroup.closure {x : M | ∃ (g : G) (a : M), x = g • a * a⁻¹}))

def galFracSubmod (σ : L ≃ₐ[K] L) (M : Submodule (𝓞 L) L) : Submodule (𝓞 L) L where
  carrier := σ '' (M : Set L)
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, map_add σ a b⟩
  zero_mem' := ⟨0, zero_mem M, map_zero σ⟩
  smul_mem' r := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(galRestrict (𝓞 K) K L (𝓞 L) σ).symm r • x, M.smul_mem _ hx, ?_⟩
    simp only [Algebra.smul_def, map_mul]
    congr 1; rw [← algebraMap_galRestrict_apply (𝓞 K) σ, AlgEquiv.apply_symm_apply]

noncomputable def galFracIdeal (σ : L ≃ₐ[K] L)
    (I : FractionalIdeal (𝓞 L)⁰ L) : FractionalIdeal (𝓞 L)⁰ L :=
  ⟨galFracSubmod K L σ (I : Submodule (𝓞 L) L), by
    obtain ⟨a, ha_mem, ha⟩ := I.2
    refine ⟨galRestrict (𝓞 K) K L (𝓞 L) σ a,
      map_mem_nonZeroDivisors _ (galRestrict (𝓞 K) K L (𝓞 L) σ).injective ha_mem, ?_⟩
    rintro b ⟨x, hx, rfl⟩; obtain ⟨c, hc⟩ := ha x hx
    exact ⟨galRestrict (𝓞 K) K L (𝓞 L) σ c, by
      simp only [Algebra.smul_def] at hc ⊢
      rw [algebraMap_galRestrict_apply (𝓞 K) σ,
        algebraMap_galRestrict_apply (𝓞 K) σ, ← map_mul, hc]⟩⟩

noncomputable def galFracIdealEquiv (σ : L ≃ₐ[K] L) :
    FractionalIdeal (𝓞 L)⁰ L ≃* FractionalIdeal (𝓞 L)⁰ L where
  toFun := galFracIdeal K L σ
  invFun := galFracIdeal K L σ⁻¹
  left_inv I := by
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
    · intro hx; exact ⟨σ x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv I := by
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
    · intro hx; exact ⟨σ⁻¹ x, ⟨x, hx, rfl⟩, by simp⟩
  map_mul' I J := by
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [galFracIdeal, FractionalIdeal.coe_mul]
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩
      exact Submodule.mul_induction_on hy
        (fun a ha b hb => by
          rw [map_mul σ a b]
          exact Submodule.mul_mem_mul
            (show σ a ∈ galFracSubmod K L σ ↑I from ⟨a, ha, rfl⟩)
            (show σ b ∈ galFracSubmod K L σ ↑J from ⟨b, hb, rfl⟩))
        (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    · intro hx
      exact Submodule.mul_induction_on hx
        (fun a ha b hb => by
          obtain ⟨a', ha', rfl⟩ := (show a ∈ galFracSubmod K L σ ↑I from ha)
          obtain ⟨b', hb', rfl⟩ := (show b ∈ galFracSubmod K L σ ↑J from hb)
          exact ⟨a' * b', Submodule.mul_mem_mul ha' hb', map_mul σ a' b'⟩)
        (fun a b ha hb => by
          obtain ⟨a', ha', rfl⟩ := ha; obtain ⟨b', hb', rfl⟩ := hb
          exact ⟨a' + b', add_mem ha' hb', map_add σ a' b'⟩)

set_option maxHeartbeats 400000 in
noncomputable def galFracIdealAutHom :
    (L ≃ₐ[K] L) →* MulAut (FractionalIdeal (𝓞 L)⁰ L) where
  toFun := galFracIdealEquiv K L
  map_one' := by
    ext I : 1
    show galFracIdeal K L 1 I = I
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨x, hx, by simp⟩
  map_mul' σ τ := by
    ext I : 1
    show galFracIdeal K L (σ * τ) I = galFracIdeal K L σ (galFracIdeal K L τ I)
    apply FractionalIdeal.coeToSubmodule_injective
    ext x; simp only [galFracIdeal, galFracSubmod]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨τ z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z, hz, rfl⟩

def mulAutUnitsLift (M : Type*) [Monoid M] : MulAut M →* MulAut Mˣ where
  toFun := Units.mapEquiv
  map_one' := by ext u; simp [Units.mapEquiv]
  map_mul' f g := by ext u; simp [Units.mapEquiv]

@[reducible]
noncomputable def galActionOnFracIdealUnits_ax :
    (K : Type*) → (L : Type*) → [Field K] → [NumberField K] → [Field L] → [NumberField L] →
    [Algebra K L] → [IsGalois K L] → [FiniteDimensional K L] → [IsCyclic (L ≃ₐ[K] L)] →
    MulDistribMulAction (L ≃ₐ[K] L) (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  fun K L => MulDistribMulAction.compHom _
    ((mulAutUnitsLift _).comp (galFracIdealAutHom K L))

@[reducible]
noncomputable def galActionOnFracIdealUnits :
    MulDistribMulAction (L ≃ₐ[K] L) (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  galActionOnFracIdealUnits_ax K L

noncomputable def idealExtensionMonoidHom_ax :
    (K : Type*) → (L : Type*) → [Field K] → [NumberField K] → [Field L] → [NumberField L] →
    [Algebra K L] → [IsGalois K L] → [FiniteDimensional K L] → [IsCyclic (L ≃ₐ[K] L)] →
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  fun _K L => Units.map (FractionalIdeal.extendedHomₐ L (𝓞 L)).toMonoidHom

noncomputable def idealExtensionMonoidHom :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  idealExtensionMonoidHom_ax K L

end
