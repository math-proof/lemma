/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Def.v1.Atlas.Buildings.code.Building.InfinityConstruction
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Reflexivity of the face relation on simplices at infinity. -/
theorem SimplexAtInfinity.IsFace.refl (b : Building V) (md : ApartmentMetricData b)
    (σ : SimplexAtInfinity b md) :
    SimplexAtInfinity.IsFace b md σ σ :=
  Set.Subset.refl _

/-- Transitivity of the face relation. -/
theorem SimplexAtInfinity.IsFace.trans {b : Building V} {md : ApartmentMetricData b}
    {σ τ ρ : SimplexAtInfinity b md}
    (h₁ : SimplexAtInfinity.IsFace b md σ τ)
    (h₂ : SimplexAtInfinity.IsFace b md τ ρ) :
    SimplexAtInfinity.IsFace b md σ ρ :=
  Set.Subset.trans h₁ h₂

/-- Antisymmetry of the face relation at the point-set level. -/
theorem SimplexAtInfinity.IsFace.antisymm_points {b : Building V} {md : ApartmentMetricData b}
    {σ τ : SimplexAtInfinity b md}
    (h₁ : SimplexAtInfinity.IsFace b md σ τ)
    (h₂ : SimplexAtInfinity.IsFace b md τ σ) :
    σ.points = τ.points :=
  Set.Subset.antisymm h₁ h₂

/-- Extensionality: simplices at infinity are equal iff their point sets coincide. -/
theorem SimplexAtInfinity.ext' {b : Building V} {md : ApartmentMetricData b}
    {σ τ : SimplexAtInfinity b md}
    (h : σ.points = τ.points) : σ = τ := by
  cases σ; cases τ; simp only [SimplexAtInfinity.mk.injEq] at h ⊢; exact h

end AffineBuilding
