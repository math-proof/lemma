/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/SimplexAtInfinity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Infinity.Sectors.Part3
import Lemma.Fin.All_All_Any_And_InAndAll_In_Vertices
import Structure.v1.Atlas.Buildings.code.Building.Infinity.SimplexAtInfinity
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- The building at infinity is *spherical*: each apartment $A_\infty$ has finitely
many simplices and at least one apartment exists (Section 16.10). -/
def BuildingAtInfinity.IsSpherical (b : Building V) (md : ApartmentMetricData b)
    (Binf : BuildingAtInfinity b md) : Prop :=

  (∀ A ∈ Binf.apartments, Set.Finite A.simplices) ∧


  Binf.apartments.Nonempty

end AffineBuilding
