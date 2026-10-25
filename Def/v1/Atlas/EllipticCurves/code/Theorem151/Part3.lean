/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.WeierstrassP
import Lemma.Complex.Atlas.v1.EllipticCurves.code.WeierstrassP
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Def.v1.Atlas.EllipticCurves.code.Uniformization
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Instance.v1.Atlas.EllipticCurves.code.Theorem151.Part2
open Complex


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

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

end ComplexLattice
end
