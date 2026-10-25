/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec9Blowups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec9Blowups.Part2
open Polynomial


namespace Lec9Blowups

/-- For a surjection `φ : R → A`, the blowup algebra of `𝔪` in `A` is
isomorphic to the blowup algebra of `φ⁻¹(𝔪)` in `R` modulo the kernel
of the induced map. -/
noncomputable def blowupQuotientEquiv {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : Function.Surjective φ) (𝔪 : Ideal A) :
    (blowupAlgebra R (𝔪.comap φ)) ⧸ RingHom.ker (blowupMapRestrict φ 𝔪)
      ≃+* blowupAlgebra A 𝔪 :=
  RingHom.quotientKerEquivOfSurjective (blowupMapRestrict_surjective φ hφ 𝔪)

/-- Lec 9, Prop 13: the blowup of `A` along `𝔪` is independent of the
chosen surjective presentation of `A`. -/
noncomputable def blowup_independent_of_embedding
    {R₁ R₂ A : Type*} [CommRing R₁] [CommRing R₂] [CommRing A]
    (φ₁ : R₁ →+* A) (hφ₁ : Function.Surjective φ₁)
    (φ₂ : R₂ →+* A) (hφ₂ : Function.Surjective φ₂)
    (𝔪 : Ideal A) :
    (blowupAlgebra R₁ (𝔪.comap φ₁)) ⧸ RingHom.ker (blowupMapRestrict φ₁ 𝔪)
      ≃+*
    (blowupAlgebra R₂ (𝔪.comap φ₂)) ⧸ RingHom.ker (blowupMapRestrict φ₂ 𝔪) :=
  (blowupQuotientEquiv φ₁ hφ₁ 𝔪).trans (blowupQuotientEquiv φ₂ hφ₂ 𝔪).symm

/-- Lec 9, Prop 13 (intrinsic blowup): the blowup at a maximal ideal of
a `k`-algebra `A` is independent of the chosen surjective presentation
by a `k`-algebra `R`. -/
noncomputable def blowup_intrinsic
    (k : Type*) [Field k]
    {R₁ R₂ A : Type*} [CommRing R₁] [CommRing R₂] [CommRing A]
    [Algebra k A] [Algebra k R₁] [Algebra k R₂]
    (φ₁ : R₁ →+* A) (hφ₁ : Function.Surjective φ₁)
    (φ₂ : R₂ →+* A) (hφ₂ : Function.Surjective φ₂)
    (𝔪 : Ideal A) (_h𝔪 : 𝔪.IsMaximal) :
    (blowupAlgebra R₁ (𝔪.comap φ₁)) ⧸ RingHom.ker (blowupMapRestrict φ₁ 𝔪)
      ≃+*
    (blowupAlgebra R₂ (𝔪.comap φ₂)) ⧸ RingHom.ker (blowupMapRestrict φ₂ 𝔪) :=
  blowup_independent_of_embedding φ₁ hφ₁ φ₂ hφ₂ 𝔪

/-- The intrinsic blowup of `A` at a maximal ideal `𝔪` is naturally
isomorphic to the blowup of any `k`-algebra presentation. -/
noncomputable def blowup_intrinsic_equiv
    (k : Type*) [Field k]
    {R A : Type*} [CommRing R] [CommRing A]
    [Algebra k A] [Algebra k R]
    (φ : R →+* A) (hφ : Function.Surjective φ)
    (𝔪 : Ideal A) (_h𝔪 : 𝔪.IsMaximal) :
    (blowupAlgebra R (𝔪.comap φ)) ⧸ RingHom.ker (blowupMapRestrict φ 𝔪)
      ≃+* blowupAlgebra A 𝔪 :=
  blowupQuotientEquiv φ hφ 𝔪

end Lec9Blowups
