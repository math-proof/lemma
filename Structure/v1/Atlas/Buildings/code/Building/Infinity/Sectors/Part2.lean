/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part5
import Lemma.Set.IsBoundedImage.of.IsBounded.IsSimilitude
import Lemma.Finset.AreOpposite.of.AreOpposite
import Lemma.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
import Def.v1.Atlas.Buildings.code.Building.Spherical
import Def.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection
import Def.v1.Atlas.Buildings.code.Building.Infinity.Sectors
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- A *geodesic ray* in the affine building: a map $ℕ → V$ that is an isometric
embedding for the building distance, $d(\rho(m), \rho(n)) = |m - n|$. -/
structure GeodesicRay (b : Building V) (md : ApartmentMetricData b) where
  toFun : ℕ → V
  isometry : ∀ m n : ℕ, buildingDist b md (toFun m) (toFun n) = ((m : ℤ) - (n : ℤ)).natAbs

end AffineBuilding
