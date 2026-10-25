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
set_option maxHeartbeats 800000

open Ideal Submodule


section ValuationRingDef

theorem isValuationSubring_iff_forall_units {K : Type*} [Field K] (R : Subring K) :
    (∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) ↔ (∀ x : K, x ≠ 0 → (x ∈ R ∨ x⁻¹ ∈ R)) := by
  constructor
  · intro h x _
    exact h x
  · intro h x
    by_cases hx : x = 0
    · left; subst hx; exact R.zero_mem
    · exact h x hx


end ValuationRingDef
