/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Order.Hom.Lattice
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Theorem.v1.Atlas.NumberTheoryI.code.HenselFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
import Def.v1.Atlas.NumberTheoryI.code.LocalExtensions.Part2


section MaxUnramifiedInvariance

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

variable (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

theorem integral_closure_isLocalRing
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L] :
    IsLocalRing ↥(integralClosure A L) := by


  set B := ↥(integralClosure A L)

  haveI : IsDomain B := inferInstance
  haveI : Nontrivial B := IsDomain.toNontrivial

  have hB_not_field : ¬IsField B := by
    intro hfield
    haveI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
    have hinj : Function.Injective (algebraMap A B) := by
      have h1 : Function.Injective (algebraMap A L) := by
        rw [IsScalarTower.algebraMap_eq A K L]
        exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
      intro a b hab
      have h2 := congr_arg (algebraMap B L) hab
      simp only [← IsScalarTower.algebraMap_apply] at h2
      exact h1 h2
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField hinj hfield)

  have hmax_ne_bot : ∀ (J : Ideal B), J.IsMaximal → J ≠ ⊥ := by
    intro J hJ heq
    exact hB_not_field (Ring.isField_iff_maximal_bot.mpr (heq ▸ hJ))

  obtain ⟨𝔮, h𝔮⟩ := Ideal.exists_maximal B

  have hcomap_eq : ∀ (J : Ideal B), J.IsMaximal →
      Ideal.comap (algebraMap A B) J = IsLocalRing.maximalIdeal A := by
    intro J hJ
    have hprime : (Ideal.comap (algebraMap A B) J).IsPrime := Ideal.IsPrime.comap (algebraMap A B)
    have hne_bot : Ideal.comap (algebraMap A B) J ≠ ⊥ := by
      obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hmax_ne_bot J hJ)
      exact Ideal.comap_ne_bot_of_integral_mem hx_ne hx_mem
        (IsIntegralClosure.isIntegral A L x)
    exact IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne_bot hprime)

  have huniq : ∀ (I : Ideal B), I.IsMaximal → I = 𝔮 := by
    intro I hI
    by_contra hne

    have hne' : ¬(I ≤ 𝔮) := fun h => hne (hI.eq_of_le h𝔮.ne_top h)
    obtain ⟨b, hbI, hb𝔮⟩ := Set.not_subset.mp hne'
    have hbint : IsIntegral A b := IsIntegralClosure.isIntegral A L b
    have hirr : Irreducible (minpoly A b) := minpoly.irreducible hbint
    have hcomapI := hcomap_eq I hI
    have hcomap𝔮 := hcomap_eq 𝔮 h𝔮

    set 𝔭 := IsLocalRing.maximalIdeal A
    set f := minpoly A b
    set π := Ideal.Quotient.mk 𝔭
    set f_bar := Polynomial.map π f
    haveI h𝔭_max : 𝔭.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
    letI : Field (A ⧸ 𝔭) := Ideal.Quotient.field 𝔭

    have hcoeff0 : f.coeff 0 ∈ 𝔭 := by
      have : f.coeff 0 ∈ Ideal.comap (algebraMap A B) I := by
        rw [Ideal.mem_comap]
        have h1 : (Ideal.Quotient.mk I) (Polynomial.aeval b f) = 0 := by
          rw [minpoly.aeval, map_zero]
        rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
            Ideal.Quotient.eq_zero_iff_mem.mpr hbI, Polynomial.eval₂_at_zero] at h1
        exact Ideal.Quotient.eq_zero_iff_mem.mp h1
      rwa [hcomapI] at this

    have hf_bar_ne : f_bar ≠ 0 := (Polynomial.Monic.map π (minpoly.monic hbint)).ne_zero

    have hroot0 : f_bar.IsRoot 0 := by
      rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hcoeff0
    set d := f_bar.rootMultiplicity 0
    have hd_pos : 0 < d := (Polynomial.rootMultiplicity_pos hf_bar_ne).mpr hroot0

    obtain ⟨q, hfact, hq_ndvd⟩ := f_bar.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf_bar_ne 0
    simp only [map_zero, sub_zero] at hfact hq_ndvd

    have hcoprime : IsCoprime q (Polynomial.X ^ d) :=
      Irreducible.coprime_pow_of_not_dvd d Polynomial.irreducible_X hq_ndvd

    have hfact' : f_bar = q * Polynomial.X ^ d := by rw [hfact, mul_comm]
    rcases irreducible_no_coprime_factor_mod hirr q (Polynomial.X ^ d) hfact' hcoprime with hu | hu
    ·

      rw [Polynomial.isUnit_iff] at hu
      obtain ⟨r, hr_unit, hrq⟩ := hu

      have hlift_cond : ∀ a ∈ 𝔭, ((Ideal.Quotient.mk 𝔮).comp (algebraMap A B)) a = 0 := by
        intro a ha
        simp only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        rwa [← Ideal.mem_comap, hcomap𝔮]
      set g := Ideal.Quotient.lift 𝔭 ((Ideal.Quotient.mk 𝔮).comp (algebraMap A B)) hlift_cond
      have hg_comp : g.comp π = (Ideal.Quotient.mk 𝔮).comp (algebraMap A B) :=
        Ideal.Quotient.lift_comp_mk 𝔭 _ hlift_cond
      set b_bar := Ideal.Quotient.mk 𝔮 b
      have heval : Polynomial.eval₂ g b_bar f_bar = 0 := by
        rw [Polynomial.eval₂_map, hg_comp]
        rw [← Polynomial.hom_eval₂ f (algebraMap A B) (Ideal.Quotient.mk 𝔮) b]
        have : Polynomial.eval₂ (algebraMap A B) b f = 0 := by
          rw [← Polynomial.aeval_def]; exact minpoly.aeval A b
        rw [this, map_zero]
      have heval2 : g r * b_bar ^ d = 0 := by
        rw [hfact', ← hrq] at heval
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at heval
        exact heval
      haveI : Nontrivial (B ⧸ 𝔮) := Ideal.Quotient.nontrivial_iff.mpr h𝔮.ne_top
      haveI : IsDomain (B ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
      have hgr_ne : g r ≠ 0 := (g.isUnit_map hr_unit).ne_zero
      have hbd : b_bar ^ d = 0 := by
        rcases mul_eq_zero.mp heval2 with h | h
        · exact absurd h hgr_ne
        · exact h
      have hbz : b_bar = 0 := (pow_eq_zero_iff (by omega : d ≠ 0)).mp hbd
      exact hb𝔮 (Ideal.Quotient.eq_zero_iff_mem.mp hbz)
    ·
      rw [Polynomial.isUnit_iff] at hu
      obtain ⟨r, _, hrp⟩ := hu
      have hdeg : (Polynomial.X (R := A ⧸ 𝔭) ^ d).natDegree = 0 := by
        rw [← hrp, Polynomial.natDegree_C]
      rw [Polynomial.natDegree_X_pow] at hdeg
      omega
  exact isLocalRing_of_unique_maximal B 𝔮 h𝔮 huniq

theorem integral_closure_isNoetherianRing
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L] [Algebra.IsSeparable K L] :
    IsNoetherianRing ↥(integralClosure A L) :=
  IsIntegralClosure.isNoetherianRing A K L (integralClosure A L)

theorem integral_closure_module_finite
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L] [Algebra.IsSeparable K L] :
    Module.Finite A ↥(integralClosure A L) :=
  IsIntegralClosure.finite A K L (integralClosure A L)

end MaxUnramifiedInvariance
