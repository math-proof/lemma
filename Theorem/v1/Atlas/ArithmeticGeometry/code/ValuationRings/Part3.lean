/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Instance.v1.Atlas.ArithmeticGeometry.code.ValuationRings
set_option maxHeartbeats 800000

open Ideal Submodule


section RegularLocalDVR

open IsLocalRing Module

example (R : Type*) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    R →+* Localization.AtPrime 𝔭 :=
  algebraMap R (Localization.AtPrime 𝔭)

end LocalizationAtPrime

section Definition1620

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable example : LinearOrderedCommGroupWithZero (ValuationRing.ValueGroup R K) :=
  inferInstance

end Definition1620
