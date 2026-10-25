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
import Def.v1.Atlas.ArithmeticGeometry.code.ValuationRings
set_option maxHeartbeats 800000

open Ideal Submodule


section Theorem1618

noncomputable example (R : Type*) [CommRing R] [IsLocalRing R] :
    Field (IsLocalRing.ResidueField R) :=
  IsLocalRing.ResidueField.field R


end Theorem1618
