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
public import Def.v1.Atlas.NumberTheoryI.code.Chapter3.DedekindProperties
open Ideal

public section

section ExtendedVersion

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

variable (p : Ideal A) [p.IsPrime]

omit [IsNoetherianRing A] in
theorem nonZeroDivisors_le_comap_localizationAtPrime :
    (nonZeroDivisors A) ≤ Submonoid.comap
      (algebraMap A (Localization.AtPrime p))
      (nonZeroDivisors (Localization.AtPrime p)) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors)

end ExtendedVersion
