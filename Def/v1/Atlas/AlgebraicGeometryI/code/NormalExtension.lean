/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalExtension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.NormalExtension

@[expose] public section

namespace AlgebraicHartogs

attribute [instance] HeightOnePrime.isPrime

variable {A : Type*} [CommRing A] [IsDomain A]

/-- Equivalence between Mathlib's `HeightOneSpectrum` and our `HeightOnePrime`
structure for a Dedekind domain. -/
def equivHeightOneSpectrumPrime :
    IsDedekindDomain.HeightOneSpectrum A ≃ HeightOnePrime A where
  toFun v := ⟨v.asIdeal, v.isPrime, height_eq_one_of_prime_ne_bot v.asIdeal v.ne_bot⟩
  invFun p := ⟨p.asIdeal, p.isPrime, p.ne_bot⟩
  left_inv v := by cases v; rfl
  right_inv p := by cases p; rfl

end AlgebraicHartogs
