/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Algebra.Module.ZLattice.Basic
open Complex Module ZSpan Set


noncomputable section

/-- A complex lattice is identified with a `PeriodPair`: a pair `(ω₁, ω₂)` of complex
numbers that are linearly independent over `ℝ`, generating a rank-`2` `ℤ`-lattice in `ℂ`. -/
abbrev ComplexLattice := PeriodPair

end
