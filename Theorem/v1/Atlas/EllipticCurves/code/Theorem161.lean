/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Lattice.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lattice
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Group.Quotient
import Def.v1.Atlas.EllipticCurves.code.Theorem161


namespace ComplexLattice

noncomputable section

open Pointwise Function ZSpan

/-- The scalar `0` always sends `L₁` into `L₂`, so it lies in `latticeMulSet`. -/
theorem zero_mem_latticeMulSet (L₁ L₂ : ComplexLattice) :
    (0 : ℂ) ∈ latticeMulSet L₁ L₂ := by
  intro z _; simp [L₂.lattice.zero_mem]

end
end ComplexLattice
