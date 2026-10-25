/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/RetractionDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Retraction
import Structure.v1.Atlas.Buildings.code.Building.RetractionDef
variable {V : Type*} [DecidableEq V]


/-- A building retraction is *distance-diminishing* if for any two chambers
$C, D$ of $X$, the gallery distance in $A$ from $\rho(C)$ to $\rho(D)$ is at
most the gallery distance from $C$ to $D$ in $X$. -/
def BuildingRetraction.IsDistanceDiminishing
    {b : Building V} (ρ : BuildingRetraction b) : Prop :=
  ∀ C D, b.toChamberComplex.toSimplicialComplex.IsMaximal C →
    b.toChamberComplex.toSimplicialComplex.IsMaximal D →
    galleryDist ρ.apt (C.image ρ.map) (D.image ρ.map) ≤
    galleryDist b.toChamberComplex.toSimplicialComplex C D

