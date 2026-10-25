/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ValuationBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring


noncomputable section

open IsDedekindDomain

set_option linter.unusedSectionVars false

def ExtendsValuation
    (A : Type*) [CommRing A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L]
    (𝔭 : HeightOneSpectrum A)
    (w : Valuation L (WithZero (Multiplicative ℤ))) : Prop :=
  (w.comap (algebraMap K L)).IsEquiv (𝔭.valuation K)

section AKLB

variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

variable [Algebra A L] [IsScalarTower A K L]

variable (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
         [Algebra A B] [Algebra B L] [IsScalarTower A B L]
         [IsIntegralClosure B A L] [IsFractionRing B L]

def primesAbove (𝔭 : HeightOneSpectrum A) : Set (HeightOneSpectrum B) :=
  { 𝔮 : HeightOneSpectrum B | 𝔮.asIdeal.LiesOver 𝔭.asIdeal }

end AKLB
end
