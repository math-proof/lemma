/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/SquareClassApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.LSeries.PrimesInAP

noncomputable section

open scoped BigOperators

/-- Two elements $a, b \in \mathbb{Q}_p$ lie in the same square class if there exists a nonzero
$u \in \mathbb{Q}_p$ such that $a = b \cdot u^2$. -/
def PadicSameSquareClass (p : ℕ) [Fact (Nat.Prime p)] (a b : ℚ_[p]) : Prop :=
  ∃ u : ℚ_[p], u ≠ 0 ∧ a = b * u ^ 2

/-- Two real numbers $a, b \in \mathbb{R}$ lie in the same square class if there exists a nonzero
$u \in \mathbb{R}$ such that $a = b \cdot u^2$ (equivalently, $a$ and $b$ have the same sign). -/
def RealSameSquareClass (a b : ℝ) : Prop :=
  ∃ u : ℝ, u ≠ 0 ∧ a = b * u ^ 2
