/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/DiscreteGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace DiscreteGroups

abbrev E2 := EuclideanSpace ℝ (Fin 2)

abbrev M₂ := E2 ≃ᵃⁱ[ℝ] E2

def translationPart (f : M₂) : E2 := f 0

def linearPart (f : M₂) : E2 ≃ₗᵢ[ℝ] E2 := f.linearIsometryEquiv

def IsPureTranslation (f : M₂) : Prop :=
  linearPart f = LinearIsometryEquiv.refl ℝ E2

def rotationAngle (f : M₂) : ℝ :=
  ‖(linearPart f).toLinearIsometry.toContinuousLinearMap - ContinuousLinearMap.id ℝ E2‖

def IsDiscrete (G : Subgroup M₂) : Prop :=
  ∃ ε > 0, (∀ f ∈ G, IsPureTranslation f → f ≠ 1 → ‖translationPart f‖ ≥ ε) ∧
            (∀ f ∈ G, linearPart f ≠ LinearIsometryEquiv.refl ℝ E2 → rotationAngle f ≥ ε)

def pointGroupSet (G : Subgroup M₂) : Set (E2 ≃ₗᵢ[ℝ] E2) :=
  {A | ∃ f ∈ G, linearPart f = A}

def translationLattice (G : Subgroup M₂) : Set E2 :=
  {v : E2 | (AffineIsometryEquiv.constVAdd ℝ E2 v : M₂) ∈ G}
