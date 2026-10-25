/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ClassGroup
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Abbrev.v1.Atlas.EllipticCurves.code.CMTorsor.Part2


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
