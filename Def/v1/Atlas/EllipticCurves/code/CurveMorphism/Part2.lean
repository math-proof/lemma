/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CurveMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Inductive.v1.Atlas.EllipticCurves.code.CurveMorphism
open Polynomial

open scoped Polynomial.Bivariate

universe u


namespace CurveMorphism

variable {k : Type u} [Field k]

open ProjectiveCurve

/-- Predicate asserting that the rational map `φ` is regular at a projective
point `P`, defined by cases: at an affine point we use `IsRegularAtOver`, and at
a point at infinity we ask for a common denominator whose numerators are not all
zero. -/
def IsRegularAtProjectivePoint {f₁ f₂ : k[X][Y]}
    [IsDomain (CoordinateRing f₁)]
    (φ : ProjectiveCurve.RationalMap f₁ f₂) {K : Type u} [Field K] [Algebra k K]
    (P : ProjectiveCurvePointOver f₁ K) : Prop :=
  match P with
  | .affine Q => IsRegularAtOver φ Q
  | .atInfinity _a _b _hab =>


    ∃ (g₁ g₂ g₃ : CoordinateRing f₁)
      (h : ↥(nonZeroDivisors (CoordinateRing f₁))),
      (∃ (μ : FunctionField f₁), μ ≠ 0 ∧
        μ * φ.φ₁ = IsLocalization.mk' (FunctionField f₁) g₁ h ∧
        μ * φ.φ₂ = IsLocalization.mk' (FunctionField f₁) g₂ h ∧
        μ * φ.φ₃ = IsLocalization.mk' (FunctionField f₁) g₃ h) ∧

      (g₁ ≠ 0 ∨ g₂ ≠ 0 ∨ g₃ ≠ 0)

/-- `IsMorphism φ` says the rational map `φ` is everywhere defined, i.e. regular
at every projective point over every algebraically closed extension of `k`. This
matches Definition 4.14: a rational map that is defined everywhere is called a
morphism. -/
def IsMorphism {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]
    (φ : ProjectiveCurve.RationalMap f₁ f₂) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
    ∀ P : ProjectiveCurvePointOver f₁ K,
      IsRegularAtProjectivePoint φ P

end CurveMorphism
