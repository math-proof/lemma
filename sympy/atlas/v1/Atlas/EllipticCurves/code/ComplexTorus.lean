/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.EllipticCurves.code.Lattice
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lattice

open Complex ComplexLattice

noncomputable section

/-- The complex torus `ℂ / L` associated to a `ComplexLattice` `L`, viewed
as the quotient of the additive group of `ℂ` by the additive subgroup of lattice points. -/
abbrev ComplexTorus (L : ComplexLattice) : Type :=
  ℂ ⧸ L.toAddSubgroup

namespace ComplexTorus

variable (L : ComplexLattice)

example : AddCommGroup (ComplexTorus L) := inferInstance

/-- The canonical projection `ℂ →+ ℂ / L` sending a complex number to its class
in the complex torus, as an additive group homomorphism. -/
def proj : ℂ →+ ComplexTorus L :=
  QuotientAddGroup.mk' L.toAddSubgroup

/-- The complex torus is inhabited by the class of `0`. -/
instance : Inhabited (ComplexTorus L) :=
  ⟨0⟩

end ComplexTorus

end
