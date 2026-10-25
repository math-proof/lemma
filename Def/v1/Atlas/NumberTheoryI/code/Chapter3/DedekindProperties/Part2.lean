/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorem.v1.Atlas.NumberTheoryI.code.Chapter3.DedekindProperties
open Ideal


section ExtendedVersion

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

variable (p : Ideal A) [p.IsPrime]

noncomputable def localizationAtPrimeHom :
    FractionalIdeal (nonZeroDivisors A) (FractionRing A) →+*
    FractionalIdeal (nonZeroDivisors (Localization.AtPrime p)) (FractionRing A) :=
  FractionalIdeal.extendedHom (FractionRing A) (nonZeroDivisors_le_comap_localizationAtPrime p)

end ExtendedVersion
