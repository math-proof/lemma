/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.QuaternionBasis
public import Instance.v1.Atlas.EllipticCurves.code.EndAlgebra.Part5
public import Instance.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra.Part2
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.SimpleRing.Basic
public import Def.v1.Atlas.EllipticCurves.code.EndAlgClassification
open Module
open scoped Quaternion TensorProduct

/-- Albert's classification of finite-dimensional positive-definite involution `ℚ`-algebras `A`:
either `A = ℚ` (dimension `1`), or `A` is an imaginary quadratic field (dimension `2` with a
non-rational element squaring to a negative rational), or `A` is a definite quaternion algebra
(dimension `4` with anticommuting generators squaring to negative rationals). -/
public inductive EndAlgClassification (A : Type*) [Ring A] [Algebra ℚ A] : Prop where
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

