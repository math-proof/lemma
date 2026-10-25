/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/GateConvex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery.Part2
import Lemma.Finset.AdjacentToSimplicialComplex.of.Adjacent.In_Faces.In_Faces.In_Apartments
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace CombinatorialGeometry

/-- $\sigma$ is *gate-convex* in apartment $A$ if its chambers are maximal in $A$ and every
maximal chamber $D$ of $A$ has a gate inside $\sigma$. -/
def IsGateConvexInApartment (K : SimplicialComplex V)
    (A : SimplicialComplex V) (σ : Set (Finset V)) : Prop :=
  (∀ C ∈ σ, C ∈ A.faces ∧ A.IsMaximal C) ∧
  ∀ D, A.IsMaximal D → ∃ G ∈ σ, IsGate K σ D G

/-- A *half-apartment* of $K$ is the set of fixed chambers of some folding $f$. -/
def IsHalfApartment (K : ChamberComplex V) (_A : SimplicialComplex V)
    (H : Set (Finset V)) : Prop :=
  ∃ f : ChamberComplex.Folding K, H = f.fixedChambers

end CombinatorialGeometry
