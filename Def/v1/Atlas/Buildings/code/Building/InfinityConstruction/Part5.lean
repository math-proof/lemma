/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Theorem.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part4
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Order isomorphism: the face poset of $\sigma$ in $X_\infty$ agrees with the
face poset in any apartment $A_\infty$ containing $\sigma$. -/
noncomputable def facePosetIsoOfApartment (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (Ainf : ApartmentAtInfinity b md) (hAinf : Ainf ∈ allApartmentsAtInfinity b si md)
    (σ : SimplexAtInfinity b md) (hσ : σ ∈ Ainf.simplices) :
    OrderIso (FacePoset b md (allSimplicesAtInfinity b si md) σ)
             (FacePoset b md Ainf.simplices σ) where
  toFun := fun ⟨τ, hτ_bldg, hface⟩ =>
    ⟨τ, face_in_apartment_boundary b si md Ainf hAinf σ τ hσ hface, hface⟩
  invFun := fun ⟨τ, hτ_apt, hface⟩ =>
    ⟨τ, (apartment_simplices_sub b si md Ainf hAinf).1 hτ_apt, hface⟩
  left_inv := fun ⟨τ, _, _⟩ => by simp
  right_inv := fun ⟨τ, _, _⟩ => by simp
  map_rel_iff' := by
    intro ⟨τ₁, _, _⟩ ⟨τ₂, _, _⟩
    simp only [Equiv.coe_fn_mk]
    rfl

end AffineBuilding
