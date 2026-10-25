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
import Abbrev.v1.Atlas.EllipticCurves.code.Theorem161


namespace ComplexLattice

noncomputable section

open Pointwise Function ZSpan

/-- The canonical quotient map `ℂ → ℂ / L`, as an additive group homomorphism. -/
def proj (L : ComplexLattice) : ℂ →+ torusQuot L :=
  QuotientAddGroup.mk' L.lattice.toAddSubgroup

/-- The set `{ α ∈ ℂ : α L₁ ⊆ L₂ }` of scalars whose multiplication sends `L₁` into `L₂`. -/
def latticeMulSet (L₁ L₂ : ComplexLattice) : Set ℂ :=
  { α : ℂ | ∀ z ∈ (L₁.lattice : Set ℂ), α * z ∈ (L₂.lattice : Set ℂ) }

end
end ComplexLattice
