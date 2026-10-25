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
import Instance.v1.Atlas.ArithmeticGeometry.code.ValuationRings.Part2
set_option maxHeartbeats 800000

open Ideal Submodule


section Definition1627

variable {R : Type*} [CommRing R] {k : Type*} [Field k]

noncomputable def quotient_maximalIdealAtPoint_ringEquiv
    (φ : R →+* k) (hφ : Function.Surjective φ) :
    R ⧸ maximalIdealAtPoint φ ≃+* k :=
  RingHom.quotientKerEquivOfSurjective hφ

def localRingAtPoint_algebraMap (φ : R →+* k)
    [(maximalIdealAtPoint φ).IsPrime] :
    R →+* localRingAtPoint φ :=
  algebraMap R (localRingAtPoint φ)


end Definition1627
