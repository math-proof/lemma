/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Exponent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Real.Pi.Bounds
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies


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
