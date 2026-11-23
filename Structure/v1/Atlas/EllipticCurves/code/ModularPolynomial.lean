/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Def.v1.Atlas.EllipticCurves.code.ModularPolynomial
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup Complex


public noncomputable section

open ModularFunction

/-- A modular function for the congruence subgroup `Γ` (Definition 19.2): a function
`f : ℍ → ℂ` that is meromorphic on `ℍ`, `Γ`-invariant, and meromorphic at the cusps. -/
structure IsModularFunction (f : ℍ → ℂ) (Γ : Subgroup SL(2, ℤ)) : Prop where
  meromorphicOnH : IsMeromorphicOnH f
  invariant : IsInvariantUnder f Γ
  meromorphicAtCusps : IsMeromorphicAtCusps f

end
