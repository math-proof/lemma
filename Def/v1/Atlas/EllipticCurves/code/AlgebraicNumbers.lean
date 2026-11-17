/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Abbrev.v1.Atlas.EllipticCurves.code.AlgebraicNumbers

@[expose] public section

namespace AlgebraicNumber

/-- The ring of integers `𝓞 K` of a number field `K` is unique up to ring isomorphism:
any other integral closure `R` of `ℤ` in `K` is canonically isomorphic to `𝓞 K`. -/
noncomputable def ringOfIntegers_unique (K : Type*) [Field K] [NumberField K]
    (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    𝓞 K ≃+* R :=
  NumberField.RingOfIntegers.equiv R

end AlgebraicNumber
