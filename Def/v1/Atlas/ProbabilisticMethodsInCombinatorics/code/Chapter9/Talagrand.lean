/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Talagrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.SubGaussian
set_option maxHeartbeats 800000

open MeasureTheory Real Set Metric


namespace Talagrand

variable {n : ℕ}

/-- The Boolean cube $\{0, 1\}^n$ embedded in $\mathbb{R}^n$. -/
def cube01 (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i = 0 ∨ x i = 1}

/-- The signed cube $\{-1, +1\}^n$ embedded in $\mathbb{R}^n$. -/
def cubePM (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i = -1 ∨ x i = 1}

/-- The continuous cube $[0,1]^n$ in $\mathbb{R}^n$. -/
def continuousCube01 (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc 0 1)

/-- Talagrand's inequality for convex sets (Theorem 9.5.3) on the Boolean cube
$\{0,1\}^n$: if $A$ is convex, then
$\mu(A) \cdot \mu(\{x : \operatorname{dist}(x, A) \geq t\}) \leq e^{-t^2/4}$. -/
def IsMedian (μ : Measure (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (m : ℝ) : Prop :=
  (1 : ℝ) / 2 ≤ (μ {x | f x ≤ m}).toReal ∧ (1 : ℝ) / 2 ≤ (μ {x | m ≤ f x}).toReal

end Talagrand
