/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.EllipticCurves.code.Lattice.Part2
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.Lattice
open Complex ComplexLattice


@[expose] public noncomputable section

/-- The complex torus `ℂ / L` associated to a `ComplexLattice` `L`, viewed
as the quotient of the additive group of `ℂ` by the additive subgroup of lattice points. -/
abbrev ComplexTorus (L : ComplexLattice) : Type :=
  ℂ ⧸ L.toAddSubgroup

end
