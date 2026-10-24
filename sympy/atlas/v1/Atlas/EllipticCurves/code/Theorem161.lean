/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.EllipticCurves.code.Lattice
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lattice
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Group.Quotient

namespace ComplexLattice

noncomputable section

open Pointwise Function ZSpan

/-- The complex torus `ℂ / L` associated to a lattice `L ⊆ ℂ`. -/
abbrev torusQuot (L : ComplexLattice) : Type :=
  ℂ ⧸ L.lattice.toAddSubgroup

/-- The canonical quotient map `ℂ → ℂ / L`, as an additive group homomorphism. -/
def proj (L : ComplexLattice) : ℂ →+ torusQuot L :=
  QuotientAddGroup.mk' L.lattice.toAddSubgroup

/-- The set `{ α ∈ ℂ : α L₁ ⊆ L₂ }` of scalars whose multiplication sends `L₁` into `L₂`. -/
def latticeMulSet (L₁ L₂ : ComplexLattice) : Set ℂ :=
  { α : ℂ | ∀ z ∈ (L₁.lattice : Set ℂ), α * z ∈ (L₂.lattice : Set ℂ) }

/-- The scalar `0` always sends `L₁` into `L₂`, so it lies in `latticeMulSet`. -/
theorem zero_mem_latticeMulSet (L₁ L₂ : ComplexLattice) :
    (0 : ℂ) ∈ latticeMulSet L₁ L₂ := by
  intro z _; simp [L₂.lattice.zero_mem]

/-- Multiplication by a fixed `α : ℂ` packaged as an additive group homomorphism `ℂ →+ ℂ`. -/
def mulByAlphaHom (α : ℂ) : ℂ →+ ℂ where
  toFun z := α * z
  map_zero' := mul_zero α
  map_add' x y := mul_add α x y

/-- For `α ∈ latticeMulSet L₁ L₂`, the induced morphism `ℂ / L₁ → ℂ / L₂` between complex tori
obtained by passing multiplication-by-`α` to the quotient. -/
def inducedMap (L₁ L₂ : ComplexLattice) (α : ℂ) (hα : α ∈ latticeMulSet L₁ L₂) :
    torusQuot L₁ →+ torusQuot L₂ :=
  QuotientAddGroup.lift L₁.lattice.toAddSubgroup
    ((proj L₂).comp (mulByAlphaHom α))
    (fun z hz => by
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, proj,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, mulByAlphaHom]
      exact hα z hz)

/-- A holomorphic morphism between complex tori `ℂ / L₁ → ℂ / L₂`, packaged together with a
holomorphic lift `ℂ → ℂ` making the projection diagram commute. -/
structure ComplexTorusHolMap (L₁ L₂ : ComplexLattice) where
  toFun : torusQuot L₁ → torusQuot L₂
  lift : ℂ → ℂ
  lift_differentiable : Differentiable ℂ lift
  diagram_commutes : ∀ z : ℂ, toFun (proj L₁ z) = proj L₂ (lift z)
