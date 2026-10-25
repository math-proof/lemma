/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/ThreeChamber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery.Part2
import Lemma.Finset.AdjacentToSimplicialComplex.of.Adjacent.In_Faces.In_Faces.In_Apartments
import Lemma.Finset.GalleryDistToSimplicialComplexToChamberComplex.eq.LengthToCoxeterSystemCoxeterMatrix_Delta
import Def.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.ThreeChamber
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace CombinatorialGeometry

/-- Hypotheses underlying the three-chamber argument: concatenability of galleries and existence of
a minimal gallery between any two maximal chambers. -/
structure ThreeChamberHypotheses (b : Building V) where
  gallery_concat :
    ∀ (C₁ C₂ C₃ : Finset V)
      (g₁ g₂ : Gallery b.toSimplicialComplex),
      g₁.Connects C₁ C₂ → g₂.Connects C₂ C₃ →
      ∃ g₃ : Gallery b.toSimplicialComplex,
        g₃.Connects C₁ C₃ ∧
        g₃.length = g₁.length + g₂.length ∧
        C₂ ∈ g₃.chambers
  minimal_gallery_exists :
    ∀ (C D : Finset V),
      b.toSimplicialComplex.IsMaximal C →
      b.toSimplicialComplex.IsMaximal D →
      ∃ g : Gallery b.toSimplicialComplex,
        g.Connects C D ∧ g.length = galleryDist b.toSimplicialComplex C D

end CombinatorialGeometry
