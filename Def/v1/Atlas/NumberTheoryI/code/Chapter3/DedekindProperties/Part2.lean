/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Theorem.v1.Atlas.NumberTheoryI.code.Chapter3.DedekindProperties

@[expose] public section

open Ideal


section ExtendedVersion

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

variable (p : Ideal A) [p.IsPrime]

noncomputable def localizationAtPrimeHom :
    FractionalIdeal (nonZeroDivisors A) (FractionRing A) →+*
    FractionalIdeal (nonZeroDivisors (Localization.AtPrime p)) (FractionRing A) :=
  FractionalIdeal.extendedHom (FractionRing A) (nonZeroDivisors_le_comap_localizationAtPrime p)

end ExtendedVersion
