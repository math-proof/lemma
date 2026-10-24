/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Infinity.Sectors
import Lemma.Fin.All_All_Any_And_InAndAll_In_Vertices

set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- $f$ is bounded above on the set $S$: $∃ c, ∀ z ∈ S, f(z) ≤ c$. -/
def BoundedAboveOn (f : V → ℝ) (S : Set V) : Prop :=
  ∃ c : ℝ, ∀ z ∈ S, f z ≤ c

/-- $f$ is bounded below on $S$: $∃ c, ∀ z ∈ S, c ≤ f(z)$. -/
def BoundedBelowOn (f : V → ℝ) (S : Set V) : Prop :=
  ∃ c : ℝ, ∀ z ∈ S, c ≤ f z

/-- An *affine functional* on an apartment $A$: a function $V → ℝ$ which is affine
along the apartment's geodesic combinations. -/
structure AffineFunctional (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  toFun : V → ℝ
  affineComb : ℝ → V → V → V
  isAffine : ∀ (t : ℝ) (x y : V),
    (∃ s ∈ apartment.faces, x ∈ s) →
    (∃ s ∈ apartment.faces, y ∈ s) →
    toFun (affineComb t x y) = t * toFun x + (1 - t) * toFun y

/-- A *wall* $\eta$ in an apartment: the zero-set of an affine functional, together
with its two half-apartments $\eta^+, \eta^-$ and the axioms that the functional
is unbounded in any sector direction and has a definite sign on each sector. -/
structure Wall (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  vertices : Set V
  vertices_in_apartment : ∀ v ∈ vertices, ∃ s ∈ apartment.faces, v ∈ s
  functional : V → ℝ
  affineComb : ℝ → V → V → V
  functionalIsAffine : ∀ (t : ℝ) (x y : V),
    (∃ s ∈ apartment.faces, x ∈ s) →
    (∃ s ∈ apartment.faces, y ∈ s) →
    functional (affineComb t x y) = t * functional x + (1 - t) * functional y
  functional_vanishes : ∀ v ∈ vertices, functional v = 0
  halfPos : Set V
  halfNeg : Set V
  halfPos_def : ∀ v, (∃ s ∈ apartment.faces, v ∈ s) →
    (v ∈ halfPos ↔ 0 ≤ functional v)
  halfNeg_def : ∀ v, (∃ s ∈ apartment.faces, v ∈ s) →
    (v ∈ halfNeg ↔ functional v ≤ 0)
  halfPos_in_apartment : ∀ v ∈ halfPos, ∃ s ∈ apartment.faces, v ∈ s
  halfNeg_in_apartment : ∀ v ∈ halfNeg, ∃ s ∈ apartment.faces, v ∈ s
  functional_unbounded_on_sectors : ∀ (S : Sector b), S.apartment = apartment →
    ∀ M : ℝ, (∃ v ∈ S.vertices, functional v > M) ∨
             (∃ v ∈ S.vertices, functional v < -M)
  functional_definite_sign : ∀ (S : Sector b), S.apartment = apartment →
    ∀ (f : V → ℝ), (∀ v ∈ vertices, f v = 0) →
    (∀ v ∈ S.vertices, f S.baseVertex ≤ f v) ∨
    (∀ v ∈ S.vertices, f v ≤ f S.baseVertex)

/-- A *half-apartment*: a subset of an apartment equal to one of the canonical halves
$\eta^+$ or $\eta^-$ of some wall $\eta$. -/
structure HalfApartment (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  wall : Wall b
  wall_in_apartment : wall.apartment = apartment
  vertices : Set V
  vertices_in_apartment : ∀ v ∈ vertices, ∃ s ∈ apartment.faces, v ∈ s
  is_canonical : vertices = wall.halfPos ∨ vertices = wall.halfNeg

/-- An affine functional *vanishes on the wall* $\eta$ if it agrees on the apartment
and is zero on every wall vertex. -/
def AffineFunctional.VanishesOnWall {b : Building V}
    (af : AffineFunctional b) (eta : Wall b) : Prop :=
  af.apartment = eta.apartment ∧ ∀ v ∈ eta.vertices, af.toFun v = 0

/-- Signed distance to the wall via the chosen affine functional. -/
def signedDistToWall {b : Building V} (af : AffineFunctional b)
    (_eta : Wall b) (z : V) : ℝ :=
  af.toFun z

/-- (Unsigned) distance to the wall: absolute value of `signedDistToWall`. -/
def distToWall {b : Building V} (af : AffineFunctional b)
    (eta : Wall b) (z : V) : ℝ :=
  |signedDistToWall af eta z|

/-- The wall-distance is bounded above by some $M$ on the intersection of a sector
with a half-apartment. -/
def DistBoundedInHalfApartment {b : Building V}
    (af : AffineFunctional b) (eta : Wall b)
    (S : Sector b) (H : HalfApartment b) : Prop :=
  ∃ M : ℝ, ∀ v ∈ S.vertices, v ∈ H.vertices → distToWall af eta v ≤ M

/-- The negation of `DistBoundedInHalfApartment`: wall-distance is unbounded. -/
def DistUnboundedInHalfApartment {b : Building V}
    (af : AffineFunctional b) (eta : Wall b)
    (S : Sector b) (H : HalfApartment b) : Prop :=
  ¬ DistBoundedInHalfApartment af eta S H

/-- $H$ is the *positive* half-apartment for $(S, \eta)$: $H.\text{wall} = \eta$ and
some subsector of $S$ lies entirely in $H$. -/
def IsPositiveHalfApartment {b : Building V}
    (S : Sector b) (eta : Wall b) (H : HalfApartment b) : Prop :=
  H.wall = eta ∧ ∃ S' : Sector b, Sector.Subsector b S' S ∧ ∀ v ∈ S'.vertices, v ∈ H.vertices
