/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.NumberTheoryI.code.HenselLemmas
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselLemmas
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.LocalExtensions
import Theorem.v1.Atlas.NumberTheoryI.code.HenselFactorization
import Theorem.v1.Atlas.NumberTheoryI.code.LocalExtensions.Part2
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
import Theorem.v1.Atlas.NumberTheoryI.code.ResidueFieldFunctor


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
