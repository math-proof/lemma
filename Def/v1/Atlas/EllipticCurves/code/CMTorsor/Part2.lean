module
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.ClassGroup
public import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.Basic
public import Abbrev.v1.Atlas.EllipticCurves.code.CMTorsor.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace FieldNormTrace

section Quadratic

variable {D : ℤ}

namespace FractionalOIdeal

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

open FractionalIdeal

set_option linter.unusedSectionVars false in

/-- The ideal norm `N(𝔞) := |𝒪/𝔞|`, defined as the cardinality of the quotient ring. -/
noncomputable def idealNorm (𝔞 : Ideal 𝒪) : ℕ := Submodule.cardQuot 𝔞

/-- The norm of a fractional ideal `𝔟 = (1/d) · 𝔟.num`: `N(𝔟) = N(𝔟.num) / |N(𝔟.den)|`,
as a rational number. -/
noncomputable def fractionalIdealNorm (𝔟 : FractionalIdeal 𝒪⁰ K) : ℚ :=
  (Ideal.absNorm 𝔟.num : ℚ) / |Algebra.norm ℤ (𝔟.den : 𝒪)|

end FractionalOIdeal
end Quadratic
end FieldNormTrace
