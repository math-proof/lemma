/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Algebra.Module.ZLattice.Basic
import Theorem.v1.Atlas.EllipticCurves.code.Lattice
open Complex Module ZSpan Set


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The subgroup underlying a complex lattice carries the discrete topology induced from `ℂ`. -/
instance discreteTopology_lattice : DiscreteTopology L.lattice := inferInstance

/-- A complex lattice is a `ℤ`-lattice in `ℂ` (viewed as an `ℝ`-vector space). -/
instance isZLattice_lattice : IsZLattice ℝ L.lattice := inferInstance

end ComplexLattice
end
