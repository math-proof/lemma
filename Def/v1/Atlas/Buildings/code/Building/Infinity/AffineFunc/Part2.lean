/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Infinity.Sectors.Part3
import Lemma.Fin.All_All_Any_And_InAndAll_In_Vertices
import Structure.v1.Atlas.Buildings.code.Building.Infinity.AffineFunc
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

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

end AffineBuilding
