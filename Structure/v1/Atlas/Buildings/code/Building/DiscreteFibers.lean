/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiscreteFibers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.UniqueRetraction
import Lemma.Bijective.Any_And_In_Faces.is.Image.in.FacesAndEqImage.of.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.In_Apartments.In_Apartments
import Lemma.Finset.Any_And_All_EqAndAll_IsMaximalAndAll_EqImageSOrAdjacentAndAll_Eq.of.IsMaximal.In_Apartments
import Lemma.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
import Def.v1.Atlas.Buildings.code.AffineCoxeter.GeometricRealization.Part2
import Theorem.v1.Atlas.Buildings.code.Building.AptFoldingFromRetraction
import Def.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection
import Def.v1.Atlas.Buildings.code.Building.DiscreteFibers
set_option linter.unusedSectionVars false


noncomputable section

open Finset BigOperators

/-- A labelling-style retraction of a building $\mathcal{B}$ onto a chamber:
data of a base chamber $C$, a vertex map $\rho$ sending each face to a face
of $C$, injective on each face, and fixing $C$ pointwise. -/
structure LabellingRetraction {V : Type} [DecidableEq V] (b : Building V) where
  base : Finset V
  base_mem : base ∈ b.toChamberComplex.toSimplicialComplex.faces
  base_nonempty : base.Nonempty
  map : V → V
  map_face : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    s.image map ⊆ base ∧ (s.image map).Nonempty
  map_injOn_face : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    Set.InjOn map ↑s
  map_fixes_base : ∀ v ∈ base, map v = v

namespace DiscreteFibers

variable {V : Type} [DecidableEq V]

/-- A geometric point of the realisation $|\Delta|$ of a simplicial complex,
given as a barycentric weight function $\mathrm{wt} : V \to \mathbb{R}_{\geq 0}$
supported on a single face $\sigma$ with weights summing to $1$. -/
structure PointF (Δ : SimplicialComplex V) where
  wt : V → ℝ
  face : Finset V
  face_mem : face ∈ Δ.faces
  wt_nonneg : ∀ v, wt v ≥ 0
  wt_sum : ∑ v ∈ face, wt v = 1
  support_in_face : ∀ v, wt v ≠ 0 → v ∈ face

end DiscreteFibers
end
