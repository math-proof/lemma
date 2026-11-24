module
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Algebra.CharP.Defs
public import Def.v1.Atlas.EllipticCurves.code.ModularCurves.Part3
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.ModularCurves
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.Uniformization
public import Def.v1.Atlas.EllipticCurves.code.Uniformization
public import Def.v1.Atlas.EllipticCurves.code.ModularPolynomial.Part4
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup Complex


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open ModularFunction

section ModularCurveX0Defs

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Matrix

open scoped MatrixGroups UpperHalfPlane

namespace ExtendedUpperHalfPlane

/-- Register `smulExt` as the scalar multiplication of `SL₂(ℤ)` on `ℍ*`. -/
instance : SMul SL(2, ℤ) ExtendedUpperHalfPlane where
  smul := smulExt

/-- The `SL₂(ℤ)`-action on `ℍ*` is a `MulAction`, with `1 · x = x` and
`(g₁ g₂) · x = g₁ · (g₂ · x)`. -/
instance : MulAction SL(2, ℤ) ExtendedUpperHalfPlane where
  one_smul x := by
    show smulExt 1 x = x
    cases x with
    | inl τ =>
      show Sum.inl ((1 : SL(2, ℤ)) • τ) = Sum.inl τ
      simp [one_smul]
    | inr c =>
      show Sum.inr (cuspAction 1 c) = Sum.inr c
      simp [cuspAction_one]
  mul_smul g₁ g₂ x := by
    show smulExt (g₁ * g₂) x = smulExt g₁ (smulExt g₂ x)
    cases x with
    | inl τ =>
      show Sum.inl ((g₁ * g₂) • τ) = Sum.inl (g₁ • (g₂ • τ))
      congr 1
      exact SemigroupAction.mul_smul g₁ g₂ τ
    | inr c =>
      show Sum.inr (cuspAction (g₁ * g₂) c) = Sum.inr (cuspAction g₁ (cuspAction g₂ c))
      congr 1
      exact cuspAction_mul g₁ g₂ c

/-- Restriction of the `SL₂(ℤ)`-action on `ℍ*` to the congruence subgroup `Γ₀(N)`. -/
instance gamma0Action (N : ℕ) :
    MulAction (CongruenceSubgroup.Gamma0 N) ExtendedUpperHalfPlane :=
  MulAction.compHom ExtendedUpperHalfPlane (CongruenceSubgroup.Gamma0 N).subtype

end ExtendedUpperHalfPlane
end ModularCurveX0Defs
end
