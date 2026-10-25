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
open Complex


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- A function `f : ℂ → ℂ` is `L`-periodic if `f(z + ω) = f(z)` for every `z ∈ ℂ` and
every lattice element `ω ∈ L`. -/
def IsLatticePeriodic (f : ℂ → ℂ) : Prop :=
  ∀ ω ∈ L.lattice, ∀ z : ℂ, f (z + ω) = f z

end ComplexLattice
end
