/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop22PicCaCl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.ClassGroup
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Prop22PicCaCl


noncomputable section

open FractionalIdeal nonZeroDivisors

variable (R : Type*) [CommRing R] [IsDomain R]

/-- The Cartier-to-Picard homomorphism `DivC(R) → Pic(R)`, sending a Cartier divisor
to its associated line bundle. -/
def Prop22.cartierToPicHom :
    Prop22.DivC R →* CommRing.Pic R :=
  (ClassGroup.equivPic R).toMonoidHom.comp (ClassGroup.mk (K := FractionRing R))

/-- Proposition 22: the class group of Cartier divisors is isomorphic to the Picard
group of line bundles, `ClassGroup R ≃* Pic R`. -/
def prop22_cartier_divisors_iso_line_bundles :
    ClassGroup R ≃* CommRing.Pic R :=
  ClassGroup.equivPic R

end
