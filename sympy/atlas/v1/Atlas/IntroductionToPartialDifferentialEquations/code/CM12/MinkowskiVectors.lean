/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/MinkowskiVectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

noncomputable section

open Matrix

namespace MinkowskiVectors

/-- The Minkowski metric on $\mathbb{R}^{1+n}$ in standard coordinates,
$m_{\mu\nu} = \mathrm{diag}(-1, 1, \ldots, 1)$. -/
def minkowskiMetric (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal fun i => if i = 0 then -1 else 1

/-- The Minkowski inner product $m(X, Y) = m_{\alpha\beta} X^\alpha Y^\beta$
for vectors $X, Y \in \mathbb{R}^{1+n}$. -/
def minkowskiInner (n : ℕ) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  dotProduct X (minkowskiMetric n *ᵥ Y)

/-- A vector $X$ is timelike if $m(X, X) < 0$ (Definition 2.0.1). -/
def IsTimelike (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X < 0

/-- A vector $X$ is spacelike if $m(X, X) > 0$ (Definition 2.0.1). -/
def IsSpacelike (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X > 0

/-- A vector $X$ is null if $m(X, X) = 0$ (Definition 2.0.1). -/
def IsNull (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X = 0

/-- A vector is causal if it is timelike or null (Definition 2.0.1). -/
def IsCausal (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  IsTimelike n X ∨ IsNull n X

/-- A vector $X \in \mathbb{R}^{1+n}$ is future-directed if its time-component
$X^0$ is positive (Definition 2.0.2). -/
def IsFutureDirected (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  X 0 > 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is past-directed if its time-component
$X^0$ is negative. -/
def IsPastDirected (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  X 0 < 0

/-- A Lorentz transformation is a linear map preserving the Minkowski metric,
i.e. $\Lambda^T m \Lambda = m$ (Definition 2.1.1). -/
def IsLorentzTransformation (n : ℕ) (Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  Λᵀ * minkowskiMetric n * Λ = minkowskiMetric n
