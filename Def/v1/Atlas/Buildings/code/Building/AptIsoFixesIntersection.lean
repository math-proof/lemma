/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptIsoFixesIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.AptFoldingFromRetraction
import Lemma.Finset.Any_And_All_EqAndAll_IsMaximalAndAll_EqImageSOrAdjacentAndAll_Eq.of.IsMaximal.In_Apartments
import Lemma.Bijective.Any_And_In_Faces.is.Image.in.FacesAndEqImage.of.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.In_Apartments.In_Apartments
import Theorem.v1.Atlas.Buildings.code.Building.UniqueRetraction
open scoped Classical
open AptFoldingFromRetraction

variable {V : Type} [DecidableEq V]


/-- The canonical retraction map $\rho : V \to V$ obtained from `exists_canonical_retraction`. -/
noncomputable def retraction_map
    (b : Building V)
    (A : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_max : A.IsMaximal C) : V → V :=
  Classical.choose (exists_canonical_retraction b A hA C hC_max)

