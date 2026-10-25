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
import Theorem.v1.Atlas.EllipticCurves.code.Theorem161


namespace ComplexLattice

noncomputable section

open Pointwise Function ZSpan

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

end
end ComplexLattice
