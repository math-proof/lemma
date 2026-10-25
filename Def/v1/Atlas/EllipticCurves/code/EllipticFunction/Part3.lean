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
import Theorem.v1.Atlas.EllipticCurves.code.EllipticFunction
open Complex


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

variable {L}

variable (L) in
/-- Definition 14.9: the order of an elliptic function `f` for `L`, computed as the
sum of pole multiplicities in the fundamental parallelogram with corner `0`. -/
def ellipticOrder (f : ℂ → ℂ) (hf : L.IsEllipticFunction f) : ℕ :=
  (polesInFundParallelogram_finite hf 0).toFinset.sum (fun z => poleMultiplicity f z)

/-- The order of an elliptic function is independent of the choice of fundamental
parallelogram. -/

variable (L)

/-- `f` is a nonzero elliptic function for `L` if it is elliptic and not identically
zero. -/
def IsNonzeroElliptic (f : ℂ → ℂ) : Prop :=
  L.IsEllipticFunction f ∧ ∃ z : ℂ, f z ≠ 0

/-- The set of points in the fundamental parallelogram with corner `α` where `f` has
a nonzero `ord` (i.e., a zero or a pole). -/
def zerosAndPolesInFundParallelogram (f : ℂ → ℂ) (α : ℂ) : Set ℂ :=
  {z ∈ L.fundamentalParallelogram α | _root_.ord z f ≠ 0}

end ComplexLattice
end
