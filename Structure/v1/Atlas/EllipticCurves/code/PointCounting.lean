/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.GroupTheory.Exponent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.Real.Pi.Bounds
public import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.Isogenies


public section

section Lemma71

variable {R : Type*} [Ring R] (IsInsep : R → Prop)

/-- Abstract axiomatization of the inseparability predicate on a ring $R$
(intended to be the endomorphism ring of an elliptic curve), specifying the structural
properties needed to prove Lemma 7.1. It posits a distinguished inseparable element
$\pi$ (Frobenius) through which every inseparable endomorphism factors, closure under
multiplication by $\pi$, and closure under negation. -/
structure InsepAxioms where
  /-- The distinguished inseparable element (Frobenius). -/
  π : R
  /-- The element $\pi$ is itself inseparable. -/
  π_insep : IsInsep π
  /-- Every inseparable element factors as $\gamma \cdot \pi$ for some $\gamma$. -/
  factor : ∀ α, IsInsep α → ∃ γ, α = γ * π
  /-- Any product $\gamma \cdot \pi$ is inseparable. -/
  mul_π_insep : ∀ γ, IsInsep (γ * π)
  /-- The set of inseparable elements is closed under negation. -/
  neg_insep : ∀ α, IsInsep α → IsInsep (-α)

end Lemma71
