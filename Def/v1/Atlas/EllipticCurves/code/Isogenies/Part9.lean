/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Squarefree.Basic
import Instance.v1.Atlas.EllipticCurves.code.Isogenies.Part3
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace Isogeny

variable {F : Type u} [Field F] [DecidableEq F]

variable {E₁ E₂ E₃ : WeierstrassCurve.Affine F}

/-- Two elliptic curves are *isogenous* if there is at least one isogeny from the
first to the second. -/
def IsIsogenous (E₁ E₂ : WeierstrassCurve.Affine F) : Prop :=
  Nonempty (Isogeny E₁ E₂)

/-- Composition of isogenies: `comp ψ φ` applies `φ` then `ψ` and multiplies the
recorded degrees. -/
def comp (ψ : Isogeny E₂ E₃) (φ : Isogeny E₁ E₂) : Isogeny E₁ E₃ where
  toAddMonoidHom := ψ.toAddMonoidHom.comp φ.toAddMonoidHom
  surjective := ψ.surjective.comp φ.surjective
  degree := ψ.degree * φ.degree
  degree_pos := Nat.mul_pos ψ.degree_pos φ.degree_pos

/-- The identity isogeny on a Weierstrass curve, of degree 1. -/
def id (E : WeierstrassCurve.Affine F) : Isogeny E E where
  toAddMonoidHom := AddMonoidHom.id E.Point
  surjective := Function.surjective_id
  degree := 1
  degree_pos := Nat.one_pos

/-- An isogeny is an *isomorphism* if it admits a two-sided inverse isogeny. -/
def IsIsomorphism (φ : Isogeny E₁ E₂) : Prop :=
  ∃ (ψ : Isogeny E₂ E₁), (∀ P, ψ (φ P) = P) ∧ (∀ Q, φ (ψ Q) = Q)

/-- Two elliptic curves are *isomorphic* if there is a pair of mutually-inverse
isogenies between them. -/
def IsIsomorphic (E₁ E₂ : WeierstrassCurve.Affine F) : Prop :=
  ∃ (φ : Isogeny E₁ E₂) (ψ : Isogeny E₂ E₁),
    (∀ P, ψ (φ P) = P) ∧ (∀ Q, φ (ψ Q) = Q)

/-- The extension degree `[k(E₁) : k(E₂)]` of function fields associated to an
isogeny `φ : E₁ → E₂`, computed via `Module.finrank`. -/
noncomputable def extensionDegree
    (_φ : Isogeny E₁ E₂)
    [Algebra E₂.FunctionField E₁.FunctionField] : ℕ :=
  Module.finrank E₂.FunctionField E₁.FunctionField

end Isogeny

/-- A rational map between the Weierstrass curves underlying `E₁` and `E₂` sends
the base point (the point at infinity) of `E₁` to the base point of `E₂` if the
second coordinate `φ₂` is nonzero and the ratios `φ₁/φ₂`, `φ₃/φ₂` come from the
coordinate ring (so the rational map is regular at infinity, where the third
coordinate vanishes). -/
def ProjectiveCurve.RationalMap.SendsBasePointToBasePoint
    {F : Type u} [Field F] {E₁ E₂ : WeierstrassCurve.Affine F}
    [IsDomain (ProjectiveCurve.CoordinateRing E₁.polynomial)]
    (φ : ProjectiveCurve.RationalMap E₁.polynomial E₂.polynomial) : Prop :=
  φ.φ₂ ≠ 0 ∧
    φ.φ₁ * φ.φ₂⁻¹ ∈ Set.range
      (algebraMap (ProjectiveCurve.CoordinateRing E₁.polynomial)
        (ProjectiveCurve.FunctionField E₁.polynomial)) ∧
    φ.φ₃ * φ.φ₂⁻¹ ∈ Set.range
      (algebraMap (ProjectiveCurve.CoordinateRing E₁.polynomial)
        (ProjectiveCurve.FunctionField E₁.polynomial))

