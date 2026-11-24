module
public import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part5
public import Theorem.Set.IsBoundedImage.of.IsBounded.IsSimilitude
public import Theorem.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
public import Theorem.Finset.InjOnMap.of.In_FacesToSimplicialComplexToChamberComplex
public import Def.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection
public import Def.v1.Atlas.Buildings.code.Building.DiscreteFibers.Part2
public import Def.v1.Atlas.Buildings.code.Building.AffineMetricGR
set_option linter.unusedSectionVars false
open Classical
open ChamberComplex


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetricGR.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- A point of the geometric realisation of a building, abbreviating
`DiscreteFibers.PointF` of the underlying simplicial complex. -/
abbrev BuildingPointF (b : Building V) : Type :=
  DiscreteFibers.PointF b.toChamberComplex.toSimplicialComplex

end AffineBuilding
