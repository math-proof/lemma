module
public import Instance.v1.Atlas.NumberTheoryI.code.HenselLemmas
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.HenselLemmas
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.LocalExtensions
public import Theorem.v1.Atlas.NumberTheoryI.code.HenselFactorization
public import Theorem.v1.Atlas.NumberTheoryI.code.LocalExtensions.Part2
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Noetherian.Orzech
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Nakayama
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.LocalRing.Quotient
public import Theorem.v1.Atlas.NumberTheoryI.code.ResidueFieldFunctor


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open Polynomial IsLocalRing

section HenselRoots

variable {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]

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

end HenselRoots
end
