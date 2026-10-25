/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/HilbertClassPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.NumberTheory.Niven
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Bivariate
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
import Instance.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial


noncomputable section

open Polynomial Classical

/-- Evaluation `Φ_N(j₁, j₂)` of the classical modular polynomial at a pair of
complex `j`-invariants `(j₁, j₂)`. -/
def AreCyclicNIsogenous (j₁ j₂ : ℂ) (N : ℕ) : Prop :=
  ∃ (E₁ E₂ : WeierstrassCurve.Affine ℂ) (_ : E₁.IsElliptic) (_ : E₂.IsElliptic),
    E₁.j = j₁ ∧ E₂.j = j₂ ∧
    ∃ (φ : E₁.Point →+ E₂.Point), Function.Surjective φ ∧

      ∃ (P : E₁.Point), addOrderOf P = N ∧
        ∀ Q : E₁.Point, φ Q = 0 → ∃ k : ℤ, Q = k • P

end
