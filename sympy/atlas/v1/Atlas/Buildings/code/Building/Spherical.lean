/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Spherical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Basic
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Mathlib.Data.List.Chain

variable {V : Type*} [DecidableEq V]

/-- The set of chambers (maximal faces) of a simplicial complex $K$. -/
def SimplicialComplex.chambers (K : SimplicialComplex V) : Set (Finset V) :=
  { C | K.IsMaximal C }

/-- A building is *spherical* if every apartment has finitely many faces
(equivalently, finite diameter). -/
def Building.IsSpherical (b : Building V) : Prop :=
  ∀ A ∈ b.apartmentSystem.apartments,
    Set.Finite A.faces

/-- The *diameter* of a simplicial complex: the supremum of gallery distances
between pairs of chambers. -/
noncomputable def SimplicialComplex.diameter (K : SimplicialComplex V) : ℕ :=
  sSup { n | ∃ C D, K.IsMaximal C ∧ K.IsMaximal D ∧ galleryDist K C D = n }

/-- Two chambers $C, D$ of $K$ are *opposite* if both are chambers and their
gallery distance is maximal among all pairs of chambers in $K$. -/
def AreOpposite (K : SimplicialComplex V) (C D : Finset V) : Prop :=
  K.IsMaximal C ∧ K.IsMaximal D ∧
  ∀ C' D', K.IsMaximal C' → K.IsMaximal D' →
    galleryDist K C' D' ≤ galleryDist K C D

section AreOppositeTheorems

variable {K : SimplicialComplex V}
