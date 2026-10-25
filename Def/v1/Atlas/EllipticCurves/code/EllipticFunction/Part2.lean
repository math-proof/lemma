/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EllipticFunction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Lattice.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lattice
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexAnalysis
import Def.v1.Atlas.EllipticCurves.code.ComplexAnalysis.Part3
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Structure.v1.Atlas.EllipticCurves.code.EllipticFunction
open Complex


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

variable {L}

/-- The order of a pole of `f` at `z`: `n` if `f` has a pole of order `n` at `z`,
and `0` if `f` is holomorphic or has a zero at `z`. Extracted from
`meromorphicOrderAt` by negating and clamping to `ℕ`. -/
def poleMultiplicity (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  match meromorphicOrderAt f z with
  | ⊤ => 0
  | (n : ℤ) => (-n).toNat

/-- `f` has a pole at `z` iff its meromorphic order is strictly negative. -/
def IsPoleAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  meromorphicOrderAt f z < 0

variable (L) in
/-- The set of poles of `f` lying in the fundamental parallelogram with corner `α`. -/
def polesInFundParallelogram (f : ℂ → ℂ) (α : ℂ) : Set ℂ :=
  {z ∈ L.fundamentalParallelogram α | IsPoleAt f z}

end ComplexLattice
end
