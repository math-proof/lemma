/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.HenselLemmas
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselLemmas
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.LocalExtensions
import sympy.atlas.v1.Atlas.NumberTheoryI.code.HenselFactorization
import sympy.atlas.v1.Atlas.NumberTheoryI.code.LocalExtensions
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Algebra.Hom
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.LocalRing.Quotient

noncomputable section

open Polynomial IsLocalRing

section HenselRoots

variable {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]

lemma dvr_ker_algebraMap_absurd
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B]
    (h_le : IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A B)) : False := by
  have hDVR_B : IsDiscreteValuationRing B := inferInstance
  have h_lift : ∀ a ∈ IsLocalRing.maximalIdeal A, (algebraMap A B) a = 0 :=
    fun a ha => h_le ha
  let f : IsLocalRing.ResidueField A →+* B :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A B) h_lift
  letI algkB : Algebra (IsLocalRing.ResidueField A) B := f.toAlgebra
  have hf_comp : ∀ a : A,
      f (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) = algebraMap A B a :=
    fun a => Ideal.Quotient.lift_mk _ _ _
  have hintegral : Algebra.IsIntegral (IsLocalRing.ResidueField A) B := by
    constructor; intro b
    obtain ⟨p, hp_monic, hp_eval⟩ := (Algebra.IsIntegral.of_finite A B).isIntegral b
    refine ⟨p.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)), hp_monic.map _, ?_⟩
    show Polynomial.eval₂ f b
      (p.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) = 0
    rw [Polynomial.eval₂_map]
    have : f.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) = algebraMap A B := by
      ext a; exact hf_comp a
    rw [this]; exact hp_eval
  exact hDVR_B.not_isField B
    (@isField_of_isIntegral_of_isField' (IsLocalRing.ResidueField A) B _ _ _ algkB hintegral
      (Field.toIsField (IsLocalRing.ResidueField A)))

section ResidueFieldFunctor

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable {B₁ : Type*} [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁]
  [Algebra A B₁] [IsLocalHom (algebraMap A B₁)] [Module.Finite A B₁]
variable {B₂ : Type*} [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂]
  [Algebra A B₂] [IsLocalHom (algebraMap A B₂)] [Module.Finite A B₂]

omit [HenselianLocalRing A] [IsLocalHom (algebraMap A B₁)] [Module.Finite A B₁] in
lemma algHom_dvr_isLocalHom (φ : B₁ →ₐ[A] B₂) : IsLocalHom φ.toRingHom := by

  apply ((local_hom_TFAE φ.toRingHom).out 3 0).mp

  have hP_prime : ((maximalIdeal B₂).comap φ.toRingHom).IsPrime :=
    Ideal.comap_isPrime φ.toRingHom (maximalIdeal B₂)

  have hP_contains : ∀ a ∈ maximalIdeal A,
      algebraMap A B₁ a ∈ (maximalIdeal B₂).comap φ.toRingHom := by
    intro a ha
    show φ.toRingHom (algebraMap A B₁ a) ∈ maximalIdeal B₂
    rw [show φ.toRingHom (algebraMap A B₁ a) = algebraMap A B₂ a from φ.commutes a]
    exact map_nonunit (algebraMap A B₂) a ha


  have hP_ne_bot : (maximalIdeal B₂).comap φ.toRingHom ≠ ⊥ := by
    intro hP_bot
    have : maximalIdeal A ≤ RingHom.ker (algebraMap A B₂) := by
      intro a ha
      have h1 := hP_contains a ha
      rw [hP_bot] at h1
      simp only [Ideal.mem_bot] at h1
      show algebraMap A B₂ a = 0
      rw [← φ.commutes a, h1, map_zero]
    exact dvr_ker_algebraMap_absurd A B₂ this

  have hP_max : ((maximalIdeal B₂).comap φ.toRingHom).IsMaximal :=
    @IsPrime.to_maximal_ideal B₁ _ _ _ _ hP_prime hP_ne_bot

  exact (IsLocalRing.eq_maximalIdeal hP_max) ▸ le_refl _

end ResidueFieldFunctor

def residueFieldFunctorAlg (φ : B₁ →ₐ[A] B₂) :
    ResidueField B₁ →ₐ[ResidueField A] ResidueField B₂ :=
  { @ResidueField.map B₁ B₂ _ _ _ _ φ.toRingHom (algHom_dvr_isLocalHom φ) with
    commutes' := by
      intro x
      obtain ⟨a, rfl⟩ := residue_surjective x
      show (@ResidueField.map B₁ B₂ _ _ _ _ φ.toRingHom (algHom_dvr_isLocalHom φ))
        (algebraMap (ResidueField A) (ResidueField B₁) (residue A a)) =
        algebraMap (ResidueField A) (ResidueField B₂) (residue A a)
      change (residue B₂) (φ (algebraMap A B₁ a)) = (residue B₂) (algebraMap A B₂ a)
      rw [φ.commutes] }
