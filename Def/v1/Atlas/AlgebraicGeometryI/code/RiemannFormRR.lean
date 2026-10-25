/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannFormRR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochGeneral
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
open scoped TensorProduct


noncomputable section

namespace RiemannFormRR

/-- `ℓ(D) := dim_k Hom_A(I, A)`, the dimension of the space of regular sections
of the line bundle attached to a divisor with associated ideal `I`. -/
def lD (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] (I : Ideal A) : ℕ :=
  Module.finrank k (↥I →ₗ[A] A)

/-- `ℓ(K − D) := dim_k Hom_A(I, Ω[A/k])`, the dimension of regular sections of
the differential twist `K − D`, the Serre dual. -/
def lKD (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] (I : Ideal A) : ℕ :=
  Module.finrank k (↥I →ₗ[A] Ω[A⁄k])

/-- The Euler characteristic `ℓ(D) − ℓ(K−D)`, the left-hand side of the
Riemann–Roch formula. -/
def divisorEulerChar (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] (I : Ideal A) : ℤ :=
  (lD k A I : ℤ) - (lKD k A I : ℤ)

/-- Predicate: `A` satisfies Riemann–Roch (Cor 30) — for every nonzero ideal
`I` the Euler characteristic equals `deg D + 1 − g`. -/
def SatisfiesRiemannRoch (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : Prop :=
  ∀ (I : Ideal A), I ≠ ⊥ →
    divisorEulerChar k A I =
      (RiemannRochGeneral.lineBundleDegree k A I : ℤ) + 1 -
      (RiemannRochGeneral.arithmeticGenus k A : ℤ)

/-- Identification `Hom_A(A, M) ≃ M`: the case `I = ⊤` of the Hom-bundle, used
to compute `ℓ(⊤) = dim_k A`. -/
def homTopEquiv (k : Type*) [Field k] (A : Type*) [CommRing A]
    [Algebra k A] (M : Type*) [AddCommGroup M] [Module A M]
    [Module k M] [SMulCommClass A k M] :
    (↥(⊤ : Ideal A) →ₗ[A] M) ≃ₗ[k] M :=
  (LinearEquiv.congrLeft M k (Submodule.topEquiv (R := A))).trans
    (LinearMap.ringLmapEquivSelf A k M)

end RiemannFormRR
end
