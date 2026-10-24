/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Convexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Basic
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import sympy.atlas.v1.Atlas.Buildings.code.Building.RetractionDef

open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- $S$ is *gallery-convex* in $K$ if every minimal gallery between two chambers of $S$ has all of
its chambers in $S$. -/
def IsGalleryConvex (K : SimplicialComplex V) (S : Set (Finset V)) : Prop :=
  ∀ C D, C ∈ S → D ∈ S →
    ∀ g : Gallery K, g.Connects C D →
    g.length = galleryDist K C D →
    ∀ E ∈ g.chambers, E ∈ S

/-- $D$ is a *gate* for chamber $C$ inside $S$ if $D \in S$ and $D$ minimizes the gallery distance
from $C$ over chambers in $S$. -/
def IsGate (K : SimplicialComplex V) (S : Set (Finset V))
    (C D : Finset V) : Prop :=
  D ∈ S ∧ ∀ E ∈ S, galleryDist K C D ≤ galleryDist K C E

/-- A subcomplex $A$ of $K$ is *convex* if its set of maximal chambers is gallery-convex in $K$. -/
def IsConvexSubcomplex (K : SimplicialComplex V) (A : SimplicialComplex V)
    (_h : IsSubcomplex A K) : Prop :=
  IsGalleryConvex K { C | C ∈ A.faces ∧ A.IsMaximal C }

/-- Convex hull of two chambers $C, D$: the union of chambers occurring on some minimal gallery
from $C$ to $D$. -/
def ConvexHull (K : SimplicialComplex V) (C D : Finset V) : Set (Finset V) :=
  { E : Finset V | ∃ g : Gallery K, g.Connects C D ∧
    g.length = galleryDist K C D ∧ E ∈ g.chambers }
