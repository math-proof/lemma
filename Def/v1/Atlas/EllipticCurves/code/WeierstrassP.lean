/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeierstrassP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Lattice.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lattice
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EisensteinSeries
import Def.v1.Atlas.EllipticCurves.code.EisensteinSeries
open Complex PeriodPair


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The Weierstrass `℘`-function associated to the complex lattice `L`, packaged
as a function `ℂ → ℂ`. -/
def weierstrassPFun (z : ℂ) : ℂ := L.weierstrassP z

/-- The derivative `℘'` of the Weierstrass `℘`-function as a function `ℂ → ℂ`. -/
def derivWeierstrassPFun (z : ℂ) : ℂ := L.derivWeierstrassP z

/-- The invariant `g₂` of the lattice, defined as `60` times the Eisenstein
series of weight `4`. -/
def g₂Fun : ℂ := 60 * L.eisensteinSeries 4

/-- The invariant `g₃` of the lattice, defined as `140` times the Eisenstein
series of weight `6`. -/
def g₃Fun : ℂ := 140 * L.eisensteinSeries 6

end ComplexLattice
end
