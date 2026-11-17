/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem161.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.EllipticCurves.code.Lattice.Part2
public import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lattice
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Algebra.Group.Quotient
public import Def.v1.Atlas.EllipticCurves.code.Theorem161.Part2


namespace ComplexLattice

public noncomputable section

open Pointwise Function ZSpan

/-- A holomorphic morphism between complex tori `ℂ / L₁ → ℂ / L₂`, packaged together with a
holomorphic lift `ℂ → ℂ` making the projection diagram commute. -/
structure ComplexTorusHolMap (L₁ L₂ : ComplexLattice) where
  toFun : torusQuot L₁ → torusQuot L₂
  lift : ℂ → ℂ
  lift_differentiable : Differentiable ℂ lift
  diagram_commutes : ∀ z : ℂ, toFun (proj L₁ z) = proj L₂ (lift z)

end
end ComplexLattice
