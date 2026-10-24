/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuaternionBasis
import sympy.atlas.v1.Atlas.EllipticCurves.code.EndAlgebra
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndAlgebra
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndomorphismAlgebra
import sympy.atlas.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.SimpleRing.Basic

open Module
open scoped Quaternion TensorProduct

/-- A `ℚ`-algebra `A` equipped with an anti-involution `invol` together with a positive-definite
reduced norm `normMap : A → ℚ` satisfying `a * invol a = normMap a`. This abstracts the structure
of the Rosati involution on the endomorphism algebra of an abelian variety. -/
class PositiveDefiniteInvolutionAlgebra (A : Type*) [Ring A] [Algebra ℚ A] where
  invol : A → A
  invol_invol : ∀ a : A, invol (invol a) = a
  invol_add : ∀ a b : A, invol (a + b) = invol a + invol b
  invol_mul : ∀ a b : A, invol (a * b) = invol b * invol a
  invol_one : invol 1 = 1
  invol_rat : ∀ q : ℚ, invol ((algebraMap ℚ A) q) = (algebraMap ℚ A) q
  normMap : A → ℚ
  normMap_spec : ∀ a : A, a * invol a = (algebraMap ℚ A) (normMap a)
  normMap_pos : ∀ a : A, a ≠ 0 → 0 < normMap a

namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- The reduced trace `tr(a) = N(a + 1) - N(a) - 1`, induced by the reduced norm. -/
noncomputable def traceMap (a : A) : ℚ :=
  normMap (a + 1) - normMap a - 1

end PositiveDefiniteInvolutionAlgebra

/-- Albert's classification of finite-dimensional positive-definite involution `ℚ`-algebras `A`:
either `A = ℚ` (dimension `1`), or `A` is an imaginary quadratic field (dimension `2` with a
non-rational element squaring to a negative rational), or `A` is a definite quaternion algebra
(dimension `4` with anticommuting generators squaring to negative rationals). -/
inductive EndAlgClassification (A : Type*) [Ring A] [Algebra ℚ A] : Prop where
  | rational (h : finrank ℚ A = 1) : EndAlgClassification A
  | imaginaryQuadratic (hdim : finrank ℚ A = 2)
      (hα : ∃ α : A, (∀ q : ℚ, α ≠ (algebraMap ℚ A) q) ∧
            ∃ d : ℚ, d < 0 ∧ α * α = (algebraMap ℚ A) d) :
      EndAlgClassification A
  | quaternionAlgebra (hdim : finrank ℚ A = 4)
      (hαβ : ∃ α β : A,
            (∃ a : ℚ, a < 0 ∧ α * α = (algebraMap ℚ A) a) ∧
            (∃ b : ℚ, b < 0 ∧ β * β = (algebraMap ℚ A) b) ∧
            α * β = -(β * α)) :
      EndAlgClassification A
