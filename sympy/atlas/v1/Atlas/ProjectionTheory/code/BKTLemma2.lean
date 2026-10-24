/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BKTLemma2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators
open Finset

noncomputable section

namespace MultiplicativeConvolution

variable {G : Type*} [Fintype G] [Group G]

/-- Multiplicative (group) convolution of two functions `f, g : G → ℂ` on a finite group `G`,
defined by `(f *_M g)(a) = ∑_{b ∈ G} f(b) · g(a · b⁻¹)`. -/
def mulConv (f g : G → ℂ) (a : G) : ℂ :=
  ∑ b : G, f b * g (a * b⁻¹)

/-- The $L^2$ norm of a function `f : G → ℂ` on a finite group, i.e. `‖f‖₂ = √(∑_b ‖f b‖²)`. -/
def l2Norm (f : G → ℂ) : ℝ :=
  Real.sqrt (∑ b : G, ‖f b‖ ^ 2)

/-- For a fixed `a ∈ G`, the map `b ↦ a · b⁻¹` is a bijection of `G` to itself. This is used
to reindex sums in convolution estimates. -/
def mulInvEquiv (a : G) : G ≃ G where
  toFun b := a * b⁻¹
  invFun b := (a⁻¹ * b)⁻¹
  left_inv b := by simp
  right_inv b := by simp
