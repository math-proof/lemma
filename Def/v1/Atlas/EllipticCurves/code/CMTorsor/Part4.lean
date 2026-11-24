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
public import Instance.v1.Atlas.EllipticCurves.code.CMTorsor


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

/-- The conjugate of an ideal `I ⊆ ℤ√d`: the image of `I` under the conjugation ring
homomorphism `star`. -/
def conjIdeal (I : Ideal (ℤ√d)) : Ideal (ℤ√d) :=
  Ideal.map (starRingEnd (ℤ√d)) I

/-- The ideal norm in `ℤ√d`, given by the cardinality of the quotient `(ℤ√d) / I`. -/
noncomputable def idealNormZsqrtd (I : Ideal (ℤ√d)) : ℕ :=
  Nat.card ((ℤ√d) ⧸ I)

/-- Characterisation of properness for nonzero fractional ideals of `ℤ√d` (imaginary
quadratic case): `I` is proper iff `I` is invertible. -/
noncomputable def fractionalIdealNormZsqrtd (hd : d < 0) [IsDomain (ℤ√d)]
    (K : Type*) [Field K] [Algebra (ℤ√d) K] [IsFractionRing (ℤ√d) K]
    (𝔞 : FractionalIdeal (ℤ√d)⁰ K) : ℚ :=
  (idealNormZsqrtd 𝔞.num : ℚ) / |(Zsqrtd.norm (𝔞.den : ℤ√d) : ℚ)|

end FractionalOIdeal
end Quadratic
end FieldNormTrace
