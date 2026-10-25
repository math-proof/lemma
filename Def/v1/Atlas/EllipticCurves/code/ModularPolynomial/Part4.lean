/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.CharP.Defs
import Def.v1.Atlas.EllipticCurves.code.ModularCurves.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ModularCurves
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Def.v1.Atlas.EllipticCurves.code.Uniformization
import Theorem.v1.Atlas.EllipticCurves.code.ModularPolynomial.Part2
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup Complex


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
