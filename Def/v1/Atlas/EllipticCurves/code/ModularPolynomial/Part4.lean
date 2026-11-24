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
public import Theorem.v1.Atlas.EllipticCurves.code.ModularPolynomial.Part2
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

/-- The `SL₂(ℤ)`-action on `ℍ*`, defined cases-wise: the Möbius action on the upper
half-plane component, and `cuspAction` on the cusp component. -/
def smulExt (γ : SL(2, ℤ)) (x : ExtendedUpperHalfPlane) : ExtendedUpperHalfPlane :=
  match x with
  | Sum.inl τ => Sum.inl (γ • τ)
  | Sum.inr c => Sum.inr (cuspAction γ c)

end ExtendedUpperHalfPlane
end ModularCurveX0Defs
end
