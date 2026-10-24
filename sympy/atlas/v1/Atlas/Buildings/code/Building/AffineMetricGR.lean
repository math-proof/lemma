/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetricGR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.AffineMetric
import Lemma.Set.IsBoundedImage.of.IsBounded.IsSimilitude
import Lemma.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.InjOnMap.of.In_FacesToSimplicialComplexToChamberComplex
import sympy.atlas.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection
import sympy.atlas.v1.Atlas.Buildings.code.Building.DiscreteFibers

set_option linter.unusedSectionVars false

open Classical
open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- Distance between two points $p$, $q$ of the geometric realisation of an
apartment, obtained by linearly extending the vertex distance using the
barycentric weights of $p$ and $q$. -/
noncomputable def aptDistGR (b : Building V) (md : ApartmentMetricData b)
    (A : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments })
    (p q : DiscreteFibers.PointF A.val) : ℝ :=
  ∑ u ∈ p.face, ∑ v ∈ q.face, p.wt u * q.wt v * md.dist_fn A u v

/-- Variant of `aptDistGR` taking weight functions and faces directly, useful for
proofs that bypass the bundled `PointF` structure. -/
noncomputable def aptDistGR' (b : Building V) (md : ApartmentMetricData b)
    (A : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments })
    (wtp wtq : V → ℝ) (σ τ : Finset V) : ℝ :=
  ∑ u ∈ σ, ∑ v ∈ τ, wtp u * wtq v * md.dist_fn A u v

/-- A point of the geometric realisation of a building, abbreviating
`DiscreteFibers.PointF` of the underlying simplicial complex. -/
abbrev BuildingPointF (b : Building V) : Type :=
  DiscreteFibers.PointF b.toChamberComplex.toSimplicialComplex

/-- A point of the building lies in some apartment if its supporting face is a
face of one of the apartments of the system. -/
def pointInApartment (b : Building V) (p : BuildingPointF b) :=
  ∃ (A : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments }),
    p.face ∈ A.val.faces

end AffineBuilding
