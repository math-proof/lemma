/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/HenselLemmas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.HenselDefs
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselDefs

open Polynomial IsLocalRing Ring

section CompleteDVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

noncomputable instance completeDVR_henselianLocalRing : HenselianLocalRing A where
  is_henselian := by
    intro f hf a₀ h₁ h₂
    exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk _))

end CompleteDVR

section HenselSimpleRootLifting

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
