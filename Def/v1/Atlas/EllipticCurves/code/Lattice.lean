/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Algebra.Module.ZLattice.Basic
import Abbrev.v1.Atlas.EllipticCurves.code.Lattice
open Complex Module ZSpan Set


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- Construct a complex lattice from two periods `ω₁`, `ω₂ : ℂ` together with a proof
that they are linearly independent over `ℝ`. -/
def mk' (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) : ComplexLattice :=
  PeriodPair.mk ω₁ ω₂ h

end ComplexLattice
end
