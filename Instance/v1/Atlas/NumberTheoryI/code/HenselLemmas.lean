/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/HenselLemmas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Def.v1.Atlas.NumberTheoryI.code.HenselDefs
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.HenselDefs
@[expose] public section

open Polynomial IsLocalRing Ring


section CompleteDVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

noncomputable instance completeDVR_henselianLocalRing : HenselianLocalRing A where
  is_henselian := by
    intro f hf a₀ h₁ h₂
    exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk _))

end CompleteDVR
