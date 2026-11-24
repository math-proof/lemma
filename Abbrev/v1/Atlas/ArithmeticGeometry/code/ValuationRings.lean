module
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Def.v1.Atlas.ArithmeticGeometry.code.ValuationRings.Part3
set_option maxHeartbeats 800000
open Ideal Submodule


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
section Definition1627

variable {R : Type*} [CommRing R] {k : Type*} [Field k]

abbrev localRingAtPoint (φ : R →+* k) [(maximalIdealAtPoint φ).IsPrime] :=
  Localization.AtPrime (maximalIdealAtPoint φ)

end Definition1627
