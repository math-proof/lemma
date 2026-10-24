/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.EllipticCurves.code.WeierstrassP
import Lemma.Complex.Atlas.v1.EllipticCurves.code.WeierstrassP
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import sympy.atlas.v1.Atlas.EllipticCurves.code.Uniformization
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open Complex

noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The Weierstrass curve `E_L : y^2 = 4x^3 - g₂(L)·x - g₃(L)` associated to a
lattice `L`, presented in long Weierstrass form with coefficients
`(a₁, a₂, a₃, a₄, a₆) = (0, 0, 0, -g₂/4, -g₃/4)`. -/
def ellipticCurveEL : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -(L.g₂ / 4), -(L.g₃ / 4)⟩

/-- The affine model of `ellipticCurveEL L`, used to talk about its affine
`Point` type. -/
def ellipticCurveEL_affine : WeierstrassCurve.Affine ℂ :=
  L.ellipticCurveEL.toAffine

/-- The type of points on the elliptic curve `E_L` associated to the lattice `L`. -/
abbrev ELPoint : Type := L.ellipticCurveEL_affine.Point

/-- The additive group structure on `E_L(ℂ)` from the chord-tangent law on a
Weierstrass curve. -/
instance : AddCommGroup L.ELPoint := by
  classical
  exact WeierstrassCurve.Affine.Point.instAddCommGroup

/-- The uniformization map on a non-lattice point: send `z ∉ L` to the affine
point `(℘(z), ℘'(z)/2)` of `E_L`. -/
def PhiAux (z : ℂ) (hz : z ∉ (L.lattice : Set ℂ)) : L.ELPoint :=
  WeierstrassCurve.Affine.Point.some
    (L.weierstrassPFun z) (L.derivWeierstrassPFun z / 2)
    (L.weierstrassP_point_nonsingular z hz)

/-- The complex torus `ℂ / L` for the lattice `L`. -/
abbrev complexTorus : Type := ℂ ⧸ L.toAddSubgroup

/-- The complex torus inherits the additive group structure from the quotient
of `ℂ` by `L`. -/
instance : AddCommGroup L.complexTorus :=
  QuotientAddGroup.Quotient.addCommGroup L.toAddSubgroup

/-- The set-theoretic uniformization lift `ℂ → E_L(ℂ)` underlying `Φ`: lattice
points are sent to the identity, and any other `z` to `(℘(z), ℘'(z)/2)`. -/
def PhiLift (z : ℂ) : L.ELPoint := by
  classical
  exact if hz : z ∈ (L.lattice : Set ℂ) then 0
    else L.PhiAux z hz

/-- The uniformization map `Φ : ℂ/L → E_L(ℂ)` as a function, obtained by
descending `PhiLift` to the quotient using its `L`-periodicity. -/
def PhiFun : L.complexTorus → L.ELPoint :=
  Quot.lift (L.PhiLift) <| by
    intro a b hab
    have hab' := hab
    change (QuotientAddGroup.leftRel L.toAddSubgroup).r a b at hab'
    rw [QuotientAddGroup.leftRel_apply] at hab'

    have hω : -a + b ∈ (L.lattice : Set ℂ) := hab'
    have : b = a + (-a + b) := by ring
    rw [this]
    exact (L.PhiLift_add_lattice a (-a + b) hω).symm

/-- Additivity of the uniformization map: `Φ(a + b) = Φ(a) + Φ(b)` on the
complex torus. This is the group-homomorphism content of Theorem 15.1, the
classical addition law for the Weierstrass `℘` function. -/
class. This is the surjectivity half of Theorem 15.1. -/
end ComplexLattice

end
