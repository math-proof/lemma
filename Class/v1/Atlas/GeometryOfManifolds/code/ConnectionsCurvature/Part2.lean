/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Def.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part4
open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- A graded form algebra: a commutative ring with a notion of homogeneous degree-$p$ elements,
projection maps onto each degree, and the usual graded multiplication property. Used to encode
the bidegree structure of $\Omega^\bullet(M)$. -/
class IsGradedFormAlgebra (R : Type*) [CommRing R] where
  IsHomog : R → ℕ → Prop
  one_homog : IsHomog 1 0
  zero_homog : ∀ p, IsHomog 0 p
  neg_homog : ∀ {a : R} {p : ℕ}, IsHomog a p → IsHomog (-a) p
  add_homog : ∀ {a b : R} {p : ℕ}, IsHomog a p → IsHomog b p → IsHomog (a + b) p
  mul_homog : ∀ {a b : R} {p q : ℕ}, IsHomog a p → IsHomog b q → IsHomog (a * b) (p + q)
  proj : ℕ → R → R
  proj_self : ∀ {a : R} {p : ℕ}, IsHomog a p → proj p a = a
  proj_other : ∀ {a : R} {p q : ℕ}, IsHomog a p → p ≠ q → proj q a = 0
  proj_homog : ∀ (p : ℕ) (a : R), IsHomog (proj p a) p

