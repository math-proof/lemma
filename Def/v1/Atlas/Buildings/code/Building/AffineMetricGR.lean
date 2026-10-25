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

end AffineBuilding
