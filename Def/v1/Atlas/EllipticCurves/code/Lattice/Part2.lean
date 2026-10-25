/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Algebra.Module.ZLattice.Basic
import Instance.v1.Atlas.EllipticCurves.code.Lattice
open Complex Module ZSpan Set


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- A `ℤ`-basis of the lattice of size `2`, given by the two periods of `L`. -/
def intBasis : Module.Basis (Fin 2) ℤ L.lattice := L.latticeBasis

/-- The `ℤ`-linear equivalence between the lattice `L` and `ℤ × ℤ` provided by the
basis of periods. -/
def equivIntProd : L.lattice ≃ₗ[ℤ] ℤ × ℤ := L.latticeEquivProd

/-- The complex lattice viewed as an additive subgroup of `ℂ`. -/
def toAddSubgroup : AddSubgroup ℂ := L.lattice.toAddSubgroup

/-- The lattice as a set: all complex numbers of the form `a • ω₁ + b • ω₂` with
`a, b ∈ ℤ`. -/
def toSet : Set ℂ := {z : ℂ | ∃ a b : ℤ, z = a • L.ω₁ + b • L.ω₂}

/-- A complex lattice `L` is normalized if `ω₂ / ω₁` lies in the upper half plane,
i.e. its imaginary part is positive. -/
def IsNormalized : Prop :=
  0 < (L.ω₂ / L.ω₁).im

section Homothety

open Pointwise

/-- Two complex lattices `L` and `L'` are homothetic if there is a nonzero complex
scalar `c` such that `L'` (as a set in `ℂ`) equals `c • L`. -/
def IsHomothetic (L L' : ComplexLattice) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)

/-- The discriminant `g₂³ - 27·g₃²` of the Weierstrass cubic associated to the lattice. -/
def discriminantLattice : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

/-- The `j`-invariant of a complex lattice, given by `1728 g₂³ / Δ` where `Δ` is the
discriminant. -/
def jInvariantLattice : ℂ := 1728 * L.g₂ ^ 3 / L.discriminantLattice

/-- The fundamental parallelogram translated by `α`: the image of the fundamental
domain of `L` under translation by `α`. -/
def fundamentalParallelogram (α : ℂ) : Set ℂ :=
  (α + ·) '' ZSpan.fundamentalDomain L.basis

/-- The quotient `ℂ / L` is in bijection with the fundamental domain of the lattice:
every coset has a unique representative in the fundamental parallelogram. -/
def quotientEquivFundDomain :
    ℂ ⧸ L.lattice ≃ ZSpan.fundamentalDomain L.basis := by
  rw [L.lattice_eq_span_range_basis]
  exact ZSpan.quotientEquiv L.basis

end Homothety
end ComplexLattice
end
