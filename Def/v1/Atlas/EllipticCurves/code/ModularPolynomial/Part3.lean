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
public import Theorem.v1.Atlas.EllipticCurves.code.ModularPolynomial
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

/-- The extended upper half-plane `ℍ*` = `ℍ ⊔ ℚ ∪ {∞}`, obtained by adjoining the
rational cusps and the cusp at infinity to `ℍ`. -/
def ExtendedUpperHalfPlane := ℍ ⊕ (WithTop ℚ)

namespace ExtendedUpperHalfPlane

/-- Inclusion `ℍ ↪ ℍ*`. -/
def ofUHP (τ : ℍ) : ExtendedUpperHalfPlane := Sum.inl τ

/-- Inclusion of a rational cusp `r ∈ ℚ ↪ ℍ*`. -/
def ofRat (r : ℚ) : ExtendedUpperHalfPlane := Sum.inr (↑r)

/-- The cusp at infinity in `ℍ*`. -/
def cuspInfty : ExtendedUpperHalfPlane := Sum.inr ⊤

/-- The action of `SL₂(ℤ)` on the cusps `ℚ ∪ {∞}`, given by the linear-fractional
formula `γ · r = (ar + b)/(cr + d)` and `γ · ∞ = a/c` (with `c = 0` mapping to `∞`). -/
def cuspAction (γ : SL(2, ℤ)) : WithTop ℚ → WithTop ℚ
  | ⊤ => if sl2zEntry γ 1 0 = 0 then ⊤ else ↑(sl2zEntry γ 0 0 / sl2zEntry γ 1 0)
  | (r : ℚ) => if sl2zEntry γ 1 0 * r + sl2zEntry γ 1 1 = 0 then ⊤
      else ↑((sl2zEntry γ 0 0 * r + sl2zEntry γ 0 1) / (sl2zEntry γ 1 0 * r + sl2zEntry γ 1 1))

end ExtendedUpperHalfPlane
end ModularCurveX0Defs
end
