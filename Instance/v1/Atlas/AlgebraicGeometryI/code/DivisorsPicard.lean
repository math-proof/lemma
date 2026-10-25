/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Def.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard


noncomputable section

open scoped nonZeroDivisors

namespace DivisorsPicard

/-- Localizing a Dedekind domain at a non-zero prime gives a DVR. -/
instance dedekind_localization_dvr (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime P) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP _

/-- Localizing a Dedekind domain at a non-zero prime gives a PID. -/
instance dedekind_localization_pid (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) :
    IsPrincipalIdealRing (Localization.AtPrime P) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    dedekind_localization_dvr R P hP
  exact inferInstance


/-- Polynomial rings in arbitrarily many variables over a field are UFDs. -/
instance mvPolynomial_ufd (k : Type*) [Field k] (σ : Type*) :
    UniqueFactorizationMonoid (MvPolynomial σ k) :=
  MvPolynomial.uniqueFactorizationMonoid σ


end DivisorsPicard
end
