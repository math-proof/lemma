/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Def.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part2
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Partial order on `FacePoset` induced by the face relation on simplices at infinity. -/
instance FacePoset.instPartialOrder (b : Building V) (md : ApartmentMetricData b)
    (S : Set (SimplexAtInfinity b md)) (σ : SimplexAtInfinity b md) :
    PartialOrder (FacePoset b md S σ) where
  le τ₁ τ₂ := SimplexAtInfinity.IsFace b md τ₁.val τ₂.val
  le_refl τ := SimplexAtInfinity.IsFace.refl b md τ.val
  le_trans _ _ _ h₁ h₂ := SimplexAtInfinity.IsFace.trans h₁ h₂
  le_antisymm τ₁ τ₂ h₁ h₂ :=
    Subtype.ext (SimplexAtInfinity.ext' (SimplexAtInfinity.IsFace.antisymm_points h₁ h₂))

end AffineBuilding
