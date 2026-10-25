/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Def.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part4
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Apartments-at-infinity admit greatest lower bounds for pairs of simplices. -/
structure BuildingAtInfinity.IsSimplicialComplex {b : Building V}
    {md : ApartmentMetricData b} (Binf : BuildingAtInfinity b md) : Prop where
  face_lattice_powerset :
    ∀ (σ : SimplexAtInfinity b md), σ ∈ Binf.simplices →
    ∃ (n : ℕ),
      Nonempty (OrderIso (WithBot (FacePoset b md Binf.simplices σ)) (Finset (Fin n)))
  glb_exists :
    ∀ (σ₁ σ₂ : SimplexAtInfinity b md),
      σ₁ ∈ Binf.simplices → σ₂ ∈ Binf.simplices →
      ∃ (γ : SimplexAtInfinity b md), γ ∈ Binf.simplices ∧
        SimplexAtInfinity.IsFace b md γ σ₁ ∧
        SimplexAtInfinity.IsFace b md γ σ₂ ∧
        (∀ (δ : SimplexAtInfinity b md), δ ∈ Binf.simplices →
          SimplexAtInfinity.IsFace b md δ σ₁ →
          SimplexAtInfinity.IsFace b md δ σ₂ →
          SimplexAtInfinity.IsFace b md δ γ)

end AffineBuilding
