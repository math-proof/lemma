/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityDedekind.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology

open scoped TensorProduct
open nonZeroDivisors

noncomputable section


namespace SerreDualityDedekind

/-- `h⁰` of the ideal sheaf `I` on a Dedekind curve, defined as the `k`-dimension
of `I` viewed as a submodule. -/
def h0_ideal (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (I : Ideal A) : ℕ :=
  Module.finrank k (I : Submodule A A)

/-- `h¹` of the ideal sheaf `I`, defined via Serre duality as the `k`-dimension
of `Hom_A(I, Ω_{A/k})`. -/
def h1_ideal (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (I : Ideal A) : ℕ :=
  Module.finrank k ((I : Submodule A A) →ₗ[A] Ω[A⁄k])


/-- `Hom_A(⊤, Ω_{A/k}) ≃ₗ[k] Ω_{A/k}`: evaluating at `1 ∈ A`. -/
def homTopOmegaEquivK (k : Type*) [Field k] (A : Type*) [CommRing A]
    [Algebra k A] :
    ((⊤ : Submodule A A) →ₗ[A] Ω[A⁄k]) ≃ₗ[k] Ω[A⁄k] :=
  ((LinearEquiv.arrowCongr Submodule.topEquiv
    (LinearEquiv.refl A (Ω[A⁄k]))).restrictScalars k).trans
    (LinearMap.ringLmapEquivSelf A k (Ω[A⁄k]))


/-- Euler characteristic of an ideal sheaf on a Dedekind curve:
`χ(I) = h⁰(I) − h¹(I)`. -/
def DedekindCurve.chi_ideal {k : Type*} [Field k] (C : DedekindCurve k) (I : Ideal C.A) : ℤ :=
  (h0_ideal k C.A I : ℤ) - (h1_ideal k C.A I : ℤ)


/-- Alternative name for `h¹` of an ideal sheaf, emphasizing the sheaf perspective. -/
def h1_ideal_sheaf (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (I : Ideal A) : ℕ :=
  Module.finrank k ((I : Submodule A A) →ₗ[A] Ω[A⁄k])
