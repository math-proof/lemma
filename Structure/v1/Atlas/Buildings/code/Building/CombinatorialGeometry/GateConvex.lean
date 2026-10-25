/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/GateConvex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery.Part2
import Lemma.Finset.AdjacentToSimplicialComplex.of.Adjacent.In_Faces.In_Faces.In_Apartments
import Def.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.GateConvex
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace CombinatorialGeometry

/-- Hypotheses asserting that every gate-convex subset of an apartment is a fixed-chamber set of
some folding strictly avoiding a chosen outside chamber $D$. -/
structure GateConvexHypotheses {b : Building V}
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) where
  folding_from_gate :
    ∀ (σ : Set (Finset V)),
      IsGateConvexInApartment b.toSimplicialComplex A σ →
      ∀ D, A.IsMaximal D → D ∉ σ →
      ∃ (K_A : ChamberComplex V) (_hK : K_A.toSimplicialComplex = A)
        (f : ChamberComplex.Folding K_A),
        (∀ C ∈ σ, C ∈ f.fixedChambers) ∧ D ∉ f.fixedChambers

end CombinatorialGeometry
