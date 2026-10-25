/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Conics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.HasseMinkowski
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HasseMinkowski
import Mathlib


/-- In a field $K$ with $\operatorname{char}(K) \neq 2$, the element $2$ is invertible. -/
@[reducible]
def invertibleTwoOfRingCharNeTwo (hK : ringChar K ≠ 2) : Invertible (2 : K) := by
  apply invertibleOfRingCharNotDvd
  intro (h : ringChar K ∣ 2)
  apply hK
  have hle : ringChar K ≤ 2 := Nat.le_of_dvd (by omega) h
  have hne0 : ringChar K ≠ 0 := by
    intro h0; rw [h0] at h; exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) h
  have hne1 : ringChar K ≠ 1 := by
    intro h1; exact not_subsingleton K (ringChar.ringChar_eq_one.mp h1)
  omega

variable [Invertible (2 : K)]

/-- A quadratic form $Q$ is geometrically irreducible if its associated bilinear form is left-nondegenerate (separating). This makes the associated conic absolutely irreducible. -/
def QuadraticForm.IsGeometricallyIrreducible
    {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Prop :=
  (associated (R := K) Q).SeparatingLeft

/-- The quadratic form $ax^2 + by^2 + cz^2 + dxy + exz + fyz$ on $K^3$, encoded as the matrix $\begin{pmatrix} a & d/2 & e/2 \\ d/2 & b & f/2 \\ e/2 & f/2 & c \end{pmatrix}$. -/
def generalConicQuadForm (a b c d e f : K) : QuadraticForm K (Fin 3 → K) :=
  Matrix.toQuadraticMap' !![a, d/2, e/2; d/2, b, f/2; e/2, f/2, c]


/-- Alias for `generalConicQuadForm`: the general ternary quadratic form $ax^2 + by^2 + cz^2 + dxy + exz + fyz$. -/
def generalConicForm (a b c d e f : K) : QuadraticForm K (Fin 3 → K) :=
  Matrix.toQuadraticMap' !![a, d/2, e/2; d/2, b, f/2; e/2, f/2, c]


section Theorem23

variable {K : Type*} [Field K]

/-- Stereographic projection (forward map): given a base point $(x_0, y_0, z_0)$ on the diagonal conic $aX^2 + bY^2 + cZ^2 = 0$, this maps $(U, V) \in \mathbb{P}^1$ to a point on the conic via a quadratic formula. -/
def stereoForward (a b x₀ y₀ z₀ U V : K) : Fin 3 → K := fun i =>
  match i with
  | 0 => a * x₀ * U ^ 2 + 2 * b * y₀ * U * V - b * x₀ * V ^ 2
  | 1 => -(a * y₀) * U ^ 2 + 2 * a * x₀ * U * V + b * y₀ * V ^ 2
  | 2 => -(a * z₀) * U ^ 2 - b * z₀ * V ^ 2

/-- Stereographic projection (backward map): given a point $v = (X, Y, Z)$ on the conic, projects from the base point $(x_0, y_0, z_0)$ to a point in $\mathbb{P}^1$. -/
def stereoBackward (x₀ y₀ z₀ : K) (v : Fin 3 → K) : Fin 2 → K := fun i =>
  match i with
  | 0 => v 0 * z₀ - x₀ * v 2
  | 1 => v 1 * z₀ - y₀ * v 2

end Theorem23
