/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChowsLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Theorem.v1.Atlas.AlgebraicGeometryI.code.ChowsLemma.Part2
open Polynomial


noncomputable section

universe u v

namespace ChowBlowup

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- For a surjective ring map `f : R →+* A`, the Rees algebra of `I.comap f` modulo the kernel of the
induced map is isomorphic to the Rees algebra of `I`. -/
def reesAlgebra_quotient_equiv {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : Function.Surjective f) (I : Ideal A) :
    (reesAlgebra (I.comap f)) ⧸ RingHom.ker (reesAlgebra_comap_to_rees f I)
      ≃+* reesAlgebra I :=
  RingHom.quotientKerEquivOfSurjective (reesAlgebra_comap_to_rees_surjective f hf I)

/-- The blowup of `A` along `I` is intrinsic: any two surjective presentations of `A`
yield isomorphic Rees algebra quotients. -/
def blowup_intrinsic
    {R₁ R₂ A : Type*} [CommRing R₁] [CommRing R₂] [CommRing A]
    (f₁ : R₁ →+* A) (hf₁ : Function.Surjective f₁)
    (f₂ : R₂ →+* A) (hf₂ : Function.Surjective f₂)
    (I : Ideal A) :
    (reesAlgebra (I.comap f₁)) ⧸ RingHom.ker (reesAlgebra_comap_to_rees f₁ I)
      ≃+*
    (reesAlgebra (I.comap f₂)) ⧸ RingHom.ker (reesAlgebra_comap_to_rees f₂ I) :=
  (reesAlgebra_quotient_equiv f₁ hf₁ I).trans (reesAlgebra_quotient_equiv f₂ hf₂ I).symm

/-- Specialization of `blowup_intrinsic`: the Rees algebra blowup at a maximal ideal is intrinsic
relative to any surjective `k`-algebra presentation. -/
def blowup_intrinsic_equiv
    (k : Type*) [Field k]
    {R A : Type*} [CommRing R] [CommRing A]
    [Algebra k A] [Algebra k R]
    (f : R →+* A) (hf : Function.Surjective f)
    (𝔪 : Ideal A) (_h𝔪 : 𝔪.IsMaximal) :
    (reesAlgebra (𝔪.comap f)) ⧸ RingHom.ker (reesAlgebra_comap_to_rees f 𝔪)
      ≃+* reesAlgebra 𝔪 :=
  reesAlgebra_quotient_equiv f hf 𝔪

end ChowBlowup

section ReesProperties

variable {R : Type u} [CommRing R]

end ReesProperties

section ChowsLemma

variable {R : Type u} [CommRing R]

/-- Two schemes `X` and `Y` are birational if there exists a scheme `Z` with open immersions into
both that have dense image. -/
def IsBirational (X Y : Scheme.{u}) : Prop :=
  ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧
    Dense (Set.range f.base) ∧ Dense (Set.range g.base)

/-- A scheme is projective if it admits a closed immersion into some `Proj 𝒜` for a finitely
generated graded algebra `𝒜`. -/
def IsProjectiveScheme (X : Scheme.{u}) : Prop :=
  ∃ (σ : Type u) (A : Type u)
    (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A)
    (𝒜 : ℕ → σ) (_ : GradedRing 𝒜) (_ : Algebra.FiniteType (𝒜 0) A)
    (i : X ⟶ Proj 𝒜), IsClosedImmersion i

end ChowsLemma
end
