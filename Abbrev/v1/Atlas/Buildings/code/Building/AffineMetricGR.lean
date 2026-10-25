/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetricGR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part5
import Lemma.Set.IsBoundedImage.of.IsBounded.IsSimilitude
import Lemma.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.InjOnMap.of.In_FacesToSimplicialComplexToChamberComplex
import Def.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection
import Def.v1.Atlas.Buildings.code.Building.DiscreteFibers.Part2
import Def.v1.Atlas.Buildings.code.Building.AffineMetricGR
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- A point of the geometric realisation of a building, abbreviating
`DiscreteFibers.PointF` of the underlying simplicial complex. -/
abbrev BuildingPointF (b : Building V) : Type :=
  DiscreteFibers.PointF b.toChamberComplex.toSimplicialComplex

end AffineBuilding
